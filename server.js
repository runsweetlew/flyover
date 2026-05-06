const http = require('http');
const https = require('https');
const fs = require('fs');
const path = require('path');

// ============================================
// Configuration
// ============================================
const PORT = 3000;
const HOME = { lat: 42.8703, lon: -85.4666 };
const KGRR = { lat: 42.8808, lon: -85.5228 };
const POLL_INTERVAL = 8000;
const SEARCH_DIST_NM = 50;
const SEARCH_DIST_MAX_NM = 250;
const SEARCH_DIST_STEP_NM = 50;
const KGRR_MAX_DIST_MI = 35;
const KGRR_MAX_ALT_FT = 18000;
const TRACKED_REGS = ['N61994', 'N759BJ', 'N133MC', 'N7222Q'];

// ============================================
// LiveATC Stream Configuration
// ============================================
// Known-good overrides (verified mount names that don't follow common patterns)
const ATC_KNOWN = {
  KGRR: [
    { id: 'clearance', label: 'Clr', mount: 'kgrr2_2_del' },
    { id: 'ground',    label: 'Gnd', mount: 'kgrr2_2_gnd' },
    { id: 'tower',     label: 'Twr', mount: 'kgrr2_2_twr' },
    { id: 'approach',  label: 'App', mount: 'kgrr2_2_app' },
  ],
  KDTW: [
    { id: 'ground',    label: 'Gnd', mount: 'kdtw_gnd' },
    { id: 'tower',     label: 'Twr', mount: 'kdtw_twr' },
    { id: 'approach',  label: 'App', mount: 'kdtw_app' },
    { id: 'departure', label: 'Dep', mount: 'kdtw_dep' },
  ],
  KLAN: [{ id: 'combined', label: 'All', mount: 'klan' }],
  KTVC: [{ id: 'combined', label: 'All', mount: 'ktvc' }],
  KJXN: [{ id: 'combined', label: 'All', mount: 'kjxn' }],
};

// Dynamic cache: ICAO -> { streams: [...], ts: timestamp, probing: false }
const atcCache = {};
const ATC_CACHE_TTL = 3600000; // 1 hour

// Probe a single LiveATC mount — resolves true if stream is available
function probeMount(mount) {
  return new Promise((resolve) => {
    const url = `http://d.liveatc.net/${mount}`;
    const req = http.get(url, { timeout: 5000 }, (res) => {
      // If we get 200, the stream exists
      const ok = res.statusCode === 200 || (res.statusCode >= 300 && res.statusCode < 400);
      res.destroy();
      resolve(ok);
    });
    req.on('error', () => resolve(false));
    req.on('timeout', () => { req.destroy(); resolve(false); });
  });
}

// Discover available streams for an airport by probing common mount patterns
async function discoverStreams(icao) {
  const code = icao.toLowerCase();
  // Common LiveATC mount patterns to try (ordered by likelihood)
  const candidates = [
    { id: 'combined',  label: 'All', mount: code },
    { id: 'tower',     label: 'Twr', mount: `${code}_twr` },
    { id: 'ground',    label: 'Gnd', mount: `${code}_gnd` },
    { id: 'approach',  label: 'App', mount: `${code}_app` },
    { id: 'departure', label: 'Dep', mount: `${code}_dep` },
    { id: 'clearance', label: 'Clr', mount: `${code}_del` },
    // Numbered variants (some airports use these)
    { id: 'combined2', label: 'All', mount: `${code}2` },
    { id: 'tower2',    label: 'Twr', mount: `${code}2_twr` },
    { id: 'ground2',   label: 'Gnd', mount: `${code}2_gnd` },
    { id: 'approach2', label: 'App', mount: `${code}2_app` },
  ];

  // Probe all in parallel
  const results = await Promise.all(candidates.map(async c => {
    const ok = await probeMount(c.mount);
    return ok ? c : null;
  }));

  const found = results.filter(Boolean);

  // If we found both combined and individual streams, prefer individual
  const hasIndividual = found.some(s => s.id === 'tower' || s.id === 'tower2');
  if (hasIndividual) {
    // Filter out combined streams to avoid redundancy
    return found.filter(s => s.id !== 'combined' && s.id !== 'combined2');
  }
  // If only combined, just return that
  if (found.some(s => s.id === 'combined' || s.id === 'combined2')) {
    return [found.find(s => s.id === 'combined' || s.id === 'combined2')];
  }
  return found;
}

// Get streams for an airport (cached, with auto-probe)
async function getAtcStreams(icao) {
  const key = icao.toUpperCase();
  // Known-good overrides always win
  if (ATC_KNOWN[key]) return ATC_KNOWN[key];
  // Check cache
  const cached = atcCache[key];
  if (cached && Date.now() - cached.ts < ATC_CACHE_TTL) return cached.streams;
  // Probe
  console.log(`[${ts()}] Probing LiveATC for ${key}...`);
  const streams = await discoverStreams(key);
  atcCache[key] = { streams, ts: Date.now() };
  console.log(`[${ts()}] LiveATC ${key}: found ${streams.length} stream(s)${streams.length ? ': ' + streams.map(s => s.mount).join(', ') : ''}`);
  return streams;
}

// ============================================
// State & Caches
// ============================================
let flightData = {
  closest: null, flights: [], totalInArea: 0, kgrrCount: 0,
  lastUpdate: null, source: null, error: null, weather: null
};

// Track last time each flight's position changed (icao -> timestamp)
let lastPositionChange = {};
let lastPositions = {}; // icao -> {lat, lon}

// Server-side trail storage: icao -> [[lat, lon, altFt], ...]
let serverTrails = {};
const MAX_TRAIL_POINTS = 1000; // ~2+ hours at 8s polling

// FR24 data (primary source for GRR flights)
let routeCache = {}; // icaoHex -> { origin, dest, flightNum, airlineIcao, onGround, heading, altitude, speed, lat, lon }
let fr24RawFeed = {}; // raw FR24 feed for processFR24Feed
let routeCacheTs = 0;
const ROUTE_TTL = 15000; // refresh every 15s (FR24 is now primary)

// Last known info for tracked planes (persists to disk across restarts)
const DATA_DIR = path.join(__dirname, 'data');
try { fs.mkdirSync(DATA_DIR, { recursive: true }); } catch (e) {}
const TRACKED_CACHE_FILE = path.join(DATA_DIR, 'tracked-cache.json');
let trackedLastSeen = {}; // registration -> { routeOrigin, routeDest, airport, lat, lon, altitudeFt, ts }
try {
  trackedLastSeen = JSON.parse(fs.readFileSync(TRACKED_CACHE_FILE, 'utf8'));
  console.log(`Loaded tracked cache: ${Object.keys(trackedLastSeen).join(', ')}`);
} catch (e) { /* no cache file yet */ }

const photoCache = new Map(); // icao -> { url, photographer, link, ts }
const PHOTO_TTL = 3600000; // 1 hour

let weatherCache = { data: null, ts: 0 };
const WEATHER_TTL = 300000; // 5 minutes

// ============================================
// Airline Database
// ============================================
const AIRLINES = {
  AAL: { name: 'American Airlines', iata: 'AA' },
  AAY: { name: 'Allegiant Air', iata: 'G4' },
  ACA: { name: 'Air Canada', iata: 'AC' },
  ASH: { name: 'Mesa Airlines', iata: 'YV' },
  ASQ: { name: 'CommutAir', iata: 'C5' },
  AWI: { name: 'Air Wisconsin', iata: 'ZW' },
  DAL: { name: 'Delta Air Lines', iata: 'DL' },
  EDV: { name: 'Endeavor Air', iata: '9E' },
  ENY: { name: 'Envoy Air', iata: 'MQ' },
  FDX: { name: 'FedEx', iata: 'FX' },
  FFT: { name: 'Frontier Airlines', iata: 'F9' },
  GJS: { name: 'GoJet Airlines', iata: 'G7' },
  JBU: { name: 'JetBlue', iata: 'B6' },
  JIA: { name: 'PSA Airlines', iata: 'OH' },
  NKS: { name: 'Spirit Airlines', iata: 'NK' },
  RPA: { name: 'Republic Airways', iata: 'YX' },
  SCX: { name: 'Sun Country', iata: 'SY' },
  SKW: { name: 'SkyWest Airlines', iata: 'OO' },
  SWA: { name: 'Southwest Airlines', iata: 'WN' },
  UAL: { name: 'United Airlines', iata: 'UA' },
  UPS: { name: 'UPS Airlines', iata: '5X' },
  VXP: { name: 'Avelo Airlines', iata: 'XP' },
  ABX: { name: 'ABX Air', iata: 'GB' },
  ATN: { name: 'Air Transport Intl', iata: '8C' },
  EJA: { name: 'NetJets', iata: '1I' },
  LXJ: { name: 'Flexjet', iata: 'LJ' },
};

// ============================================
// Aircraft Type Database
// ============================================
const AIRCRAFT_TYPES = {
  B738: 'Boeing 737-800', B73H: 'Boeing 737-800', B739: 'Boeing 737-900',
  B37M: 'Boeing 737 MAX 8', B38M: 'Boeing 737 MAX 8', B39M: 'Boeing 737 MAX 9',
  B752: 'Boeing 757-200', B753: 'Boeing 757-300',
  B763: 'Boeing 767-300', B764: 'Boeing 767-400',
  B772: 'Boeing 777-200', B77W: 'Boeing 777-300ER',
  B788: 'Boeing 787-8', B789: 'Boeing 787-9', B78X: 'Boeing 787-10',
  A319: 'Airbus A319', A320: 'Airbus A320', A20N: 'Airbus A320neo',
  A321: 'Airbus A321', A21N: 'Airbus A321neo',
  A332: 'Airbus A330-200', A333: 'Airbus A330-300', A339: 'Airbus A330-900neo',
  A359: 'Airbus A350-900', A35K: 'Airbus A350-1000',
  CRJ2: 'CRJ-200', CRJ7: 'CRJ-700', CRJ9: 'CRJ-900',
  E170: 'Embraer 170', E75L: 'Embraer 175', E75S: 'Embraer 175',
  E190: 'Embraer 190', E195: 'Embraer 195', E290: 'Embraer E195-E2',
  MD88: 'MD-88', MD90: 'MD-90',
  C172: 'Cessna 172', C182: 'Cessna 182', C206: 'Cessna 206',
  C208: 'Cessna Caravan', C210: 'Cessna 210', C402: 'Cessna 402',
  C510: 'Citation Mustang', C525: 'Citation CJ1', C25A: 'Citation CJ2',
  C25B: 'Citation CJ3', C56X: 'Citation Excel', C560: 'Citation V',
  C680: 'Citation Sovereign', C700: 'Citation Longitude', C750: 'Citation X',
  PA28: 'Piper Cherokee', PA32: 'Piper Saratoga', PA44: 'Piper Seminole',
  PA46: 'Piper Malibu', BE36: 'Beech Bonanza', BE58: 'Beech Baron',
  B350: 'King Air 350', BE20: 'King Air 200', BE9L: 'King Air C90',
  PC12: 'Pilatus PC-12', PC24: 'Pilatus PC-24',
  TBM7: 'TBM 700', TBM8: 'TBM 850', TBM9: 'TBM 900',
  LJ35: 'Learjet 35', LJ45: 'Learjet 45', LJ60: 'Learjet 60', LJ75: 'Learjet 75',
  GL5T: 'Global 5000', GLEX: 'Global Express', GL7T: 'Global 7500',
  GLF4: 'Gulfstream IV', GLF5: 'Gulfstream V',
  G280: 'Gulfstream G280', G550: 'Gulfstream G550', G650: 'Gulfstream G650',
  CL30: 'Challenger 300', CL35: 'Challenger 350', CL60: 'Challenger 604',
  H25B: 'Hawker 800', FA50: 'Falcon 50', FA7X: 'Falcon 7X', FA8X: 'Falcon 8X',
  E55P: 'Phenom 300', E545: 'Praetor 500', E550: 'Praetor 600',
  R44: 'Robinson R44', R66: 'Robinson R66',
  EC35: 'EC135', A139: 'AW139', S76: 'Sikorsky S-76', B429: 'Bell 429',
};

// ============================================
// Utility Functions
// ============================================
const toRad = (d) => d * Math.PI / 180;
const toDeg = (r) => r * 180 / Math.PI;

function distanceMi(lat1, lon1, lat2, lon2) {
  const R = 3958.8;
  const dLat = toRad(lat2 - lat1);
  const dLon = toRad(lon2 - lon1);
  const a = Math.sin(dLat / 2) ** 2 +
    Math.cos(toRad(lat1)) * Math.cos(toRad(lat2)) * Math.sin(dLon / 2) ** 2;
  return R * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
}

function bearingDeg(lat1, lon1, lat2, lon2) {
  const dLon = toRad(lon2 - lon1);
  const y = Math.sin(dLon) * Math.cos(toRad(lat2));
  const x = Math.cos(toRad(lat1)) * Math.sin(toRad(lat2)) -
    Math.sin(toRad(lat1)) * Math.cos(toRad(lat2)) * Math.cos(dLon);
  return (toDeg(Math.atan2(y, x)) + 360) % 360;
}

function compass(deg) {
  const dirs = ['N', 'NNE', 'NE', 'ENE', 'E', 'ESE', 'SE', 'SSE',
    'S', 'SSW', 'SW', 'WSW', 'W', 'WNW', 'NW', 'NNW'];
  return dirs[Math.round(deg / 22.5) % 16];
}

function getAirline(callsign) {
  if (!callsign || callsign.length < 3) return null;
  return AIRLINES[callsign.replace(/\s/g, '').substring(0, 3)] || null;
}

function formatFlightNumber(callsign, airline) {
  if (!callsign) return 'Unknown';
  const clean = callsign.trim();
  if (airline) return `${airline.iata} ${clean.substring(3)}`;
  return clean;
}

function formatAircraftType(code) {
  return code ? (AIRCRAFT_TYPES[code] || code) : null;
}

// ============================================
// HTTP JSON Fetcher
// ============================================
function fetchJSON(url) {
  return new Promise((resolve, reject) => {
    const mod = url.startsWith('https') ? https : http;
    const req = mod.get(url, { timeout: 10000 }, (res) => {
      if (res.statusCode !== 200) {
        reject(new Error(`HTTP ${res.statusCode}`));
        res.resume();
        return;
      }
      let data = '';
      res.on('data', (chunk) => data += chunk);
      res.on('end', () => {
        try { resolve(JSON.parse(data)); }
        catch (e) { reject(e); }
      });
    });
    req.on('error', reject);
    req.on('timeout', () => { req.destroy(); reject(new Error('Timeout')); });
  });
}

// ============================================
// Photo Fetcher (planespotters.net)
// ============================================
async function getPhoto(icao, registration) {
  if (!icao) return null;
  const hex = icao.toUpperCase();
  const cached = photoCache.get(hex);
  // Successful photos cache for 1hr; empty results only 15min so we retry sooner
  if (cached && Date.now() - cached.ts < (cached.url ? PHOTO_TTL : 900000)) return cached;

  // Try 1: by ICAO hex (prefer full resolution)
  try {
    const data = await fetchJSON(`https://api.planespotters.net/pub/photos/hex/${hex}`);
    if (data.photos && data.photos.length > 0) {
      const p = data.photos[0];
      const result = {
        url: p.src || (p.thumbnail_large ? p.thumbnail_large.src : (p.thumbnail ? p.thumbnail.src : null)),
        fullUrl: p.src || null,
        photographer: p.photographer || null,
        link: p.link || null,
        ts: Date.now()
      };
      photoCache.set(hex, result);
      return result;
    }
  } catch (err) { /* continue to fallback */ }

  // Try 2: planespotters by registration (better coverage for GA)
  if (registration) {
    try {
      const data = await fetchJSON(`https://api.planespotters.net/pub/photos/reg/${encodeURIComponent(registration)}`);
      if (data.photos && data.photos.length > 0) {
        const p = data.photos[0];
        const result = {
          url: p.src || (p.thumbnail_large ? p.thumbnail_large.src : (p.thumbnail ? p.thumbnail.src : null)),
          fullUrl: p.src || null,
          photographer: p.photographer || null,
          link: p.link || null,
          ts: Date.now()
        };
        photoCache.set(hex, result);
        return result;
      }
    } catch (err) { /* continue */ }
  }

  // Try 3: airport-data.com by ICAO hex (great GA coverage)
  try {
    const data = await fetchJSON(`https://airport-data.com/api/ac_thumb.json?m=${hex}&n=1`);
    if (data.status === 200 && data.count > 0 && data.data && data.data[0]) {
      const ad = data.data[0];
      const result = {
        url: ad.image || null,
        fullUrl: ad.link || null,
        photographer: ad.photographer || null,
        link: ad.link || null,
        ts: Date.now()
      };
      photoCache.set(hex, result);
      return result;
    }
  } catch (err) { /* continue */ }

  // Try 4: airport-data.com by registration
  if (registration) {
    try {
      const data = await fetchJSON(`https://airport-data.com/api/ac_thumb.json?r=${encodeURIComponent(registration)}&n=1`);
      if (data.status === 200 && data.count > 0 && data.data && data.data[0]) {
        const ad = data.data[0];
        const result = {
          url: ad.image || null,
          fullUrl: ad.link || null,
          photographer: ad.photographer || null,
          link: ad.link || null,
          ts: Date.now()
        };
        photoCache.set(hex, result);
        return result;
      }
    } catch (err) { /* continue */ }
  }

  const empty = { url: null, fullUrl: null, photographer: null, link: null, ts: Date.now() };
  photoCache.set(hex, empty);
  return empty;
}

// ============================================
// Weather Fetcher (aviationweather.gov METAR)
// ============================================
async function getWeather(icao) {
  const id = (icao || 'KGRR').toUpperCase();
  if (id === 'KGRR' && weatherCache.data && Date.now() - weatherCache.ts < WEATHER_TTL) {
    return weatherCache.data;
  }

  try {
    const data = await fetchJSON(`https://aviationweather.gov/api/data/metar?ids=${encodeURIComponent(id)}&format=json`);
    if (Array.isArray(data) && data.length > 0) {
      const m = data[0];
      // Parse temperature C -> F
      const tempC = m.temp != null ? m.temp : null;
      const tempF = tempC != null ? Math.round(tempC * 9 / 5 + 32) : null;
      const dewC = m.dewp != null ? m.dewp : null;
      const dewF = dewC != null ? Math.round(dewC * 9 / 5 + 32) : null;

      // Wind
      const windDir = m.wdir != null ? m.wdir : null;
      const windSpd = m.wspd != null ? m.wspd : null;
      const windGust = m.wgst != null ? m.wgst : null;

      // Visibility (statute miles)
      const visMi = m.visib != null ? m.visib : null;

      // Clouds
      const clouds = [];
      for (let i = 1; i <= 4; i++) {
        const cover = m[`cover${i}`];
        const base = m[`base${i}`];
        if (cover && cover !== 'CLR' && cover !== 'SKC') {
          const labels = { FEW: 'Few', SCT: 'Scattered', BKN: 'Broken', OVC: 'Overcast' };
          clouds.push({
            cover: labels[cover] || cover,
            coverCode: cover,
            baseFt: base != null ? base * 100 : null
          });
        }
      }

      // Flight rules
      let flightRules = 'VFR';
      const ceil = clouds.find(c => c.coverCode === 'BKN' || c.coverCode === 'OVC');
      const ceilFt = ceil ? ceil.baseFt : null;
      if ((ceilFt != null && ceilFt < 500) || (visMi != null && visMi < 1)) flightRules = 'LIFR';
      else if ((ceilFt != null && ceilFt < 1000) || (visMi != null && visMi < 3)) flightRules = 'IFR';
      else if ((ceilFt != null && ceilFt <= 3000) || (visMi != null && visMi <= 5)) flightRules = 'MVFR';

      // Altimeter
      const altim = m.altim != null ? (m.altim * 0.02953).toFixed(2) : null;

      const weather = {
        raw: m.rawOb || null,
        tempF, tempC, dewF, dewC,
        windDir, windSpd, windGust,
        visMi,
        clouds,
        ceilingFt: ceilFt,
        flightRules,
        altimeter: altim,
        observedAt: m.reportTime || null,
        wxString: m.wxString || null
      };

      if (id === 'KGRR') weatherCache = { data: weather, ts: Date.now() };
      return weather;
    }
  } catch (err) {
    console.error(`[${ts()}] Weather fetch failed: ${err.message}`);
  }
  return weatherCache.data; // Return stale data if available
}

// ============================================
// Flight Classification
// ============================================
function classifyFlight(distKGRR, altFt, vertRate) {
  if (distKGRR > KGRR_MAX_DIST_MI) return 'TRANSITING';
  if (altFt === null || altFt > KGRR_MAX_ALT_FT) return 'TRANSITING';
  if (distKGRR < 8 && altFt < 6000) return vertRate < -100 ? 'ARRIVING' : 'DEPARTING';
  if (vertRate < -300) return 'ARRIVING';
  if (vertRate > 300) return 'DEPARTING';
  if (distKGRR < 20 && altFt < 10000) return 'KGRR AREA';
  if (distKGRR < 35 && altFt < 15000 && vertRate < -100) return 'ARRIVING';
  return 'TRANSITING';
}

// ============================================
// Process adsb.lol data
// ============================================
function processAdsbLol(aircraft) {
  if (!Array.isArray(aircraft)) return [];
  return aircraft
    .filter(ac => ac.lat != null && ac.lon != null)
    .map(ac => {
      const adsbGround = ac.alt_baro === 'ground';
      const dHome = distanceMi(HOME.lat, HOME.lon, ac.lat, ac.lon);
      const dKGRR = distanceMi(KGRR.lat, KGRR.lon, ac.lat, ac.lon);
      const bHome = bearingDeg(HOME.lat, HOME.lon, ac.lat, ac.lon);
      const callsign = (ac.flight || '').trim();
      const airline = getAirline(callsign);
      const altFt = typeof ac.alt_baro === 'number' ? ac.alt_baro : (ac.alt_geom || null);
      const vertRate = ac.baro_rate || 0;
      // Merge FR24 data: routes, on_ground, runway
      const route = routeCache[(ac.hex || '').toLowerCase()];
      const routeOrigin = route ? route.origin : null;
      const routeDest = route ? route.dest : null;
      const fr24OnGround = route ? route.onGround : false;

      // Determine landing/runway status
      const heading = ac.track != null ? Math.round(ac.track) : null;
      let runway = null;
      let onGround = adsbGround || fr24OnGround;

      // Also detect on-ground via AGL if near KGRR
      if (!onGround && dKGRR < 2) {
        const agl = altFt != null ? altFt - 794 : null;
        if (agl != null && agl < 200) onGround = true;
      }

      // Determine runway when on ground at KGRR
      if (onGround && dKGRR < 3) {
        // Use FR24 heading if available (more reliable on ground), fall back to adsb.lol track
        const rwyHeading = (route && route.heading != null) ? route.heading : heading;
        runway = determineRunway(rwyHeading, ac.lat);
      }

      // Route-based classification overrides heuristic
      let status;
      if (onGround && dKGRR < 3) {
        status = routeOrigin === 'GRR' ? 'DEPARTING' : 'LANDED';
      } else if (routeDest === 'GRR') status = 'ARRIVING';
      else if (routeOrigin === 'GRR') status = 'DEPARTING';
      else status = classifyFlight(dKGRR, altFt, vertRate);

      return {
        callsign,
        flightNumber: formatFlightNumber(callsign, airline),
        airline: airline ? airline.name : null,
        aircraftType: formatAircraftType(ac.t),
        typeCode: ac.t || null,
        registration: ac.r || null,
        altitudeFt: altFt != null ? Math.round(altFt) : null,
        speedKts: ac.gs ? Math.round(ac.gs) : null,
        speedMph: ac.gs ? Math.round(ac.gs * 1.151) : null,
        heading,
        verticalRate: Math.round(vertRate),
        distHomeMi: Math.round(dHome * 10) / 10,
        distKGRRMi: Math.round(dKGRR * 10) / 10,
        bearingFromHome: Math.round(bHome),
        compassFromHome: compass(bHome),
        squawk: ac.squawk || null,
        status,
        isKGRR: status !== 'TRANSITING',
        isTracked: TRACKED_REGS.includes((ac.r || '').toUpperCase()),
        onGround,
        runway,
        routeOrigin,
        routeDest,
        lat: ac.lat, lon: ac.lon,
        icao: ac.hex
      };
    });
}

// ============================================
// Process OpenSky data (fallback)
// ============================================
function processOpenSky(states) {
  if (!Array.isArray(states)) return [];
  return states
    .filter(s => s[6] != null && s[5] != null && !s[8])
    .map(s => {
      const lat = s[6], lon = s[5];
      const dHome = distanceMi(HOME.lat, HOME.lon, lat, lon);
      const dKGRR = distanceMi(KGRR.lat, KGRR.lon, lat, lon);
      const bHome = bearingDeg(HOME.lat, HOME.lon, lat, lon);
      const callsign = (s[1] || '').trim();
      const airline = getAirline(callsign);
      const altM = s[7] || s[13];
      const altFt = altM != null ? Math.round(altM * 3.281) : null;
      const vertRateFpm = s[11] ? Math.round(s[11] * 196.85) : 0;
      const speedKts = s[9] ? Math.round(s[9] * 1.944) : null;
      const status = classifyFlight(dKGRR, altFt, vertRateFpm);

      return {
        callsign,
        flightNumber: formatFlightNumber(callsign, airline),
        airline: airline ? airline.name : null,
        aircraftType: null, typeCode: null, registration: null,
        altitudeFt: altFt,
        speedKts,
        speedMph: speedKts ? Math.round(speedKts * 1.151) : null,
        heading: s[10] != null ? Math.round(s[10]) : null,
        verticalRate: vertRateFpm,
        distHomeMi: Math.round(dHome * 10) / 10,
        distKGRRMi: Math.round(dKGRR * 10) / 10,
        bearingFromHome: Math.round(bHome),
        compassFromHome: compass(bHome),
        squawk: s[14] || null,
        status,
        isKGRR: status !== 'TRANSITING',
        isTracked: false,
        lat, lon,
        icao: s[0]
      };
    });
}

// ============================================
// Route Data (FlightRadar24)
// ============================================
async function pollRoutes() {
  if (Date.now() - routeCacheTs < ROUTE_TTL) return;
  try {
    const data = await fetchJSON('https://data-cloud.flightradar24.com/zones/fcgi/feed.js?airport=GRR');
    const routes = {};
    const rawFeed = {};
    for (const [key, val] of Object.entries(data)) {
      if (!Array.isArray(val) || val.length < 15) continue;
      const hex = (val[0] || '').toLowerCase();
      if (!hex) continue;
      routes[hex] = {
        origin: val[11] || null,
        dest: val[12] || null,
        flightNum: val[13] || null,
        airlineIcao: val[18] || null,
        onGround: val[14] === 1,
        heading: typeof val[3] === 'number' ? val[3] : null,
        altitude: typeof val[4] === 'number' ? val[4] : null,
        speed: typeof val[5] === 'number' ? val[5] : null,
        lat: val[1], lon: val[2]
      };
      rawFeed[key] = val; // preserve raw feed for processFR24Feed
    }
    routeCache = routes;
    fr24RawFeed = rawFeed;
    routeCacheTs = Date.now();
  } catch (err) {
    console.error(`[${ts()}] FR24 fetch failed: ${err.message}`);
  }
}

// Determine runway from heading at KGRR
// 08R/26L: ~80°/260° (southern parallel, lat ~42.879)
// 08L/26R: ~80°/260° (northern parallel, lat ~42.890)
// 17/35: ~170°/350°
function determineRunway(heading, lat) {
  if (heading == null) return null;
  const h = ((heading % 360) + 360) % 360;
  // Runway 08 direction (60°-100°)
  if (h >= 60 && h <= 100) return lat > 42.884 ? '08L' : '08R';
  // Runway 26 direction (240°-280°)
  if (h >= 240 && h <= 280) return lat > 42.884 ? '26R' : '26L';
  // Runway 17 direction (150°-190°)
  if (h >= 150 && h <= 190) return '17';
  // Runway 35 direction (330°-360° or 0°-10°)
  if (h >= 330 || h <= 10) return '35';
  return null;
}

// ============================================
// Process FR24 Feed into Flight Objects
// ============================================
function processFR24Feed(data) {
  const flights = [];
  for (const [key, val] of Object.entries(data)) {
    if (!Array.isArray(val) || val.length < 13) continue;
    const lat = val[1], lon = val[2];
    if (lat == null || lon == null) continue;
    const hex = (val[0] || '').toLowerCase();
    const heading = typeof val[3] === 'number' ? val[3] : null;
    const altFt = typeof val[4] === 'number' ? val[4] : null;
    const speedKts = typeof val[5] === 'number' ? val[5] : null;
    const typeCode = val[8] || null;
    const registration = val[9] || null;
    const routeOrigin = val[11] || null;
    const routeDest = val[12] || null;
    const callsign = (val[16] || val[13] || '').trim();
    const onGround = val[14] === 1;

    const dHome = distanceMi(HOME.lat, HOME.lon, lat, lon);
    const dKGRR = distanceMi(KGRR.lat, KGRR.lon, lat, lon);
    const bHome = bearingDeg(HOME.lat, HOME.lon, lat, lon);
    const airline = getAirline(callsign);

    // Determine runway when on ground at KGRR
    const runway = (onGround && dKGRR < 3) ? determineRunway(heading, lat) : null;

    // Status with on_ground awareness
    let status;
    if (onGround && dKGRR < 3) {
      status = routeOrigin === 'GRR' ? 'DEPARTING' : 'LANDED';
    } else if (routeDest === 'GRR') status = 'ARRIVING';
    else if (routeOrigin === 'GRR') status = 'DEPARTING';
    else status = classifyFlight(dKGRR, altFt, 0);

    flights.push({
      callsign,
      flightNumber: formatFlightNumber(callsign, airline) || registration || hex,
      airline: airline ? airline.name : null,
      aircraftType: formatAircraftType(typeCode),
      typeCode,
      registration,
      altitudeFt: altFt != null ? Math.round(altFt) : null,
      speedKts: speedKts != null ? Math.round(speedKts) : null,
      speedMph: speedKts != null ? Math.round(speedKts * 1.151) : null,
      heading: heading != null ? Math.round(heading) : null,
      verticalRate: 0,
      distHomeMi: Math.round(dHome * 10) / 10,
      distKGRRMi: Math.round(dKGRR * 10) / 10,
      bearingFromHome: Math.round(bHome),
      compassFromHome: compass(bHome),
      squawk: null,
      status,
      isKGRR: status !== 'TRANSITING',
      isTracked: TRACKED_REGS.includes((registration || '').toUpperCase()),
      onGround,
      runway,
      routeOrigin,
      routeDest,
      lat, lon,
      icao: hex
    });
  }
  return flights;
}

// ============================================
// Poll Flight Data
// ============================================
async function pollFlights() {
  let flights = [];
  let totalInArea = 0;

  // ── Step 1: FR24 primary — all GRR flights with on_ground, routes ──
  await pollRoutes(); // refreshes routeCache + fr24RawFeed
  const fr24Flights = processFR24Feed(fr24RawFeed);

  // ── Step 2: adsb.lol supplement — area search for nearby flights ──
  let adsbFlights = [];
  let adsbByHex = {};
  let searchDist = SEARCH_DIST_NM;
  try {
    const data = await fetchJSON(`https://api.adsb.lol/v2/lat/${HOME.lat}/lon/${HOME.lon}/dist/${searchDist}`);
    adsbFlights = processAdsbLol(data.ac || []);
    totalInArea = (data.ac || []).length;
    adsbByHex = {};
    // Also build raw adsb.lol map for enrichment (vertical rate, squawk)
    (data.ac || []).forEach(ac => {
      if (ac.hex) adsbByHex[ac.hex.toLowerCase()] = ac;
    });
  } catch (err) {
    console.error(`[${ts()}] adsb.lol area search failed: ${err.message}`);
  }

  // ── Step 3: Merge — FR24 flights take priority, enriched with adsb.lol ──
  const mergedMap = new Map(); // icao -> flight

  // Add FR24 flights first (primary source)
  fr24Flights.forEach(f => {
    // Enrich with adsb.lol data (vertical rate, squawk)
    const adsb = adsbByHex[f.icao];
    if (adsb) {
      f.verticalRate = adsb.baro_rate ? Math.round(adsb.baro_rate) : f.verticalRate;
      f.squawk = adsb.squawk || f.squawk;
      // Use adsb.lol altitude if FR24 reports 0 but plane is airborne
      if (f.altitudeFt === 0 && !f.onGround && typeof adsb.alt_baro === 'number') {
        f.altitudeFt = Math.round(adsb.alt_baro);
      }
    }
    mergedMap.set(f.icao, f);
  });

  // Add adsb.lol flights that FR24 doesn't have (transiting, non-GRR)
  adsbFlights.forEach(f => {
    if (!mergedMap.has(f.icao)) {
      mergedMap.set(f.icao, f);
    }
  });

  flights = Array.from(mergedMap.values());
  if (totalInArea === 0) totalInArea = flights.length;

  // ── Step 4: Tracked planes — FR24 by reg, then adsb.lol fallback ──
  const existingRegs = new Set(flights.map(f => f.registration).filter(Boolean));
  const missingRegs = TRACKED_REGS.filter(r => !existingRegs.has(r));
  if (missingRegs.length > 0) {
    // Try FR24 first (better coverage)
    const fr24Results = await Promise.all(missingRegs.map(reg =>
      fetchJSON(`https://data-cloud.flightradar24.com/zones/fcgi/feed.js?reg=${reg}`)
        .then(data => processFR24Feed(data))
        .catch(() => [])
    ));
    const fr24Extra = fr24Results.flat();
    const existHex = new Set(flights.map(f => f.icao));
    fr24Extra.forEach(f => { if (!existHex.has(f.icao)) flights.push(f); });

    // adsb.lol fallback for any still missing
    const stillMissing = missingRegs.filter(r =>
      !fr24Extra.find(f => (f.registration || '').toUpperCase() === r)
    );
    if (stillMissing.length > 0) {
      const adsbResults = await Promise.all(stillMissing.map(reg =>
        fetchJSON(`https://api.adsb.lol/v2/reg/${reg}`).then(d => d.ac || []).catch(() => [])
      ));
      const adsbExtra = processAdsbLol(adsbResults.flat());
      const existHex2 = new Set(flights.map(f => f.icao));
      adsbExtra.forEach(f => { if (!existHex2.has(f.icao)) flights.push(f); });
    }
  }

  // Mark tracked flights
  flights.forEach(f => { if (TRACKED_REGS.includes((f.registration || '').toUpperCase())) f.isTracked = true; });

  // Sort ALL flights by distance to house — there's always a closest plane
  const allByHome = flights.sort((a, b) => a.distHomeMi - b.distHomeMi);
  const kgrrFlights = allByHome.filter(f => f.isKGRR);

  // Update position freshness tracking
  const now = Date.now();
  const activeIcaos = new Set(allByHome.map(f => f.icao));
  allByHome.forEach(f => {
    const prev = lastPositions[f.icao];
    if (!prev || prev.lat !== f.lat || prev.lon !== f.lon) {
      lastPositionChange[f.icao] = now;
      lastPositions[f.icao] = { lat: f.lat, lon: f.lon };
    }
  });
  // Clean up stale entries
  for (const icao of Object.keys(lastPositions)) {
    if (!activeIcaos.has(icao)) { delete lastPositions[icao]; delete lastPositionChange[icao]; }
  }

  // Accumulate server-side trails for all flights
  allByHome.forEach(f => {
    if (!serverTrails[f.icao]) serverTrails[f.icao] = [];
    const trail = serverTrails[f.icao];
    const last = trail[trail.length - 1];
    if (!last || last[0] !== f.lat || last[1] !== f.lon) {
      trail.push([f.lat, f.lon, f.altitudeFt || 0]);
      if (trail.length > MAX_TRAIL_POINTS) trail.shift();
    }
  });
  // Clean up trails for planes no longer seen
  for (const icao of Object.keys(serverTrails)) {
    if (!activeIcaos.has(icao)) delete serverTrails[icao];
  }

  // Closest is nearest airborne plane to house
  // Skip: landed/on-ground planes, stale finals
  let closest = null;
  for (const f of allByHome) {
    // Use FR24 on_ground flag (authoritative) or AGL heuristic
    if (f.onGround || f.status === 'LANDED') continue;
    // Also skip very slow planes near KGRR (taxi/ground roll not caught by FR24)
    if (f.distKGRRMi < 3 && f.speedKts != null && f.speedKts < 60) continue;
    // Stale on final approach (no position update in 7s)
    const agl = f.altitudeFt != null ? f.altitudeFt - 794 : null;
    const onFinal = f.status === 'ARRIVING' && f.distKGRRMi < 5 && agl != null && agl < 2200;
    const staleSec = (now - (lastPositionChange[f.icao] || now)) / 1000;
    if (onFinal && staleSec >= 7) continue;
    closest = f; break;
  }
  if (!closest) closest = allByHome.find(f => !f.onGround) || allByHome[0] || null;

  // Build priority flights list:
  // - All airborne tracked planes (not on ground)
  // - Closest airborne KGRR flight
  // If no tracked planes airborne, fall back to closest-to-home
  const trackedAirborne = allByHome.filter(f => f.isTracked && !f.onGround);
  const closestKGRR = kgrrFlights.filter(f => !f.onGround).sort((a, b) => a.distKGRRMi - b.distKGRRMi)[0] || null;

  let priorityFlights = [];
  if (trackedAirborne.length > 0) {
    // Tracked planes + closest KGRR (always include KGRR in rotation)
    priorityFlights = [...trackedAirborne];
    if (closestKGRR && !priorityFlights.find(f => f.icao === closestKGRR.icao)) {
      priorityFlights.push(closestKGRR);
    }
  } else {
    // No tracked planes — just show closest to home
    if (closest) priorityFlights = [closest];
  }

  // Fetch photos and attach trails for all priority flights
  const photoPromises = priorityFlights.map(async f => {
    const p = await getPhoto(f.icao, f.registration);
    return { ...f, photo: p, trail: serverTrails[f.icao] || [] };
  });
  const priorityWithPhotos = await Promise.all(photoPromises);

  // Also fetch photo for closest (in case it's not in priority list)
  let closestPhoto = null;
  if (closest) {
    const existing = priorityWithPhotos.find(f => f.icao === closest.icao);
    closestPhoto = existing ? existing.photo : await getPhoto(closest.icao, closest.registration);
  }

  // Fetch weather (non-blocking)
  const weather = await getWeather();

  // Update last-seen data for tracked planes whenever visible
  allByHome.forEach(f => {
    if (!f.isTracked) return;
    const reg = (f.registration || '').toUpperCase();
    if (!reg) return;
    // Determine likely airport: dest if arriving/landed, origin if departing, or nearest by position
    let airport = null;
    if (f.routeDest && (f.status === 'ARRIVING' || f.status === 'LANDED')) airport = f.routeDest;
    else if (f.routeOrigin && f.status === 'DEPARTING') airport = f.routeOrigin;
    else if (f.routeDest) airport = f.routeDest; // best guess = destination
    trackedLastSeen[reg] = {
      routeOrigin: f.routeOrigin,
      routeDest: f.routeDest,
      airport,
      lat: f.lat, lon: f.lon,
      altitudeFt: f.altitudeFt,
      ts: Date.now()
    };
  });
  // Persist to disk
  try { fs.writeFileSync(TRACKED_CACHE_FILE, JSON.stringify(trackedLastSeen)); } catch (e) {}

  // Build tracked plane status (even when not airborne)
  const trackedStatus = TRACKED_REGS.map(reg => {
    const flight = allByHome.find(f => (f.registration || '').toUpperCase() === reg);
    const lastSeen = trackedLastSeen[reg] || null;
    return {
      registration: reg,
      airborne: !!flight && !flight.onGround,
      onGround: flight ? flight.onGround : false,
      lastSeen: !flight && lastSeen ? {
        airport: lastSeen.airport || lastSeen.routeDest,
        routeOrigin: lastSeen.routeOrigin,
        routeDest: lastSeen.routeDest,
        ago: Math.round((Date.now() - lastSeen.ts) / 60000) // minutes ago
      } : null,
      flight: flight ? {
        flightNumber: flight.flightNumber,
        airline: flight.airline,
        aircraftType: flight.aircraftType,
        typeCode: flight.typeCode,
        altitudeFt: flight.altitudeFt,
        distHomeMi: flight.distHomeMi,
        status: flight.status,
        routeOrigin: flight.routeOrigin,
        routeDest: flight.routeDest,
        runway: flight.runway
      } : null
    };
  });

  const landedCount = allByHome.filter(f => f.status === 'LANDED').length;

  flightData = {
    closest: closest ? { ...closest, photo: closestPhoto, trail: serverTrails[closest.icao] || [] } : null,
    priorityFlights: priorityWithPhotos,
    flights: allByHome,
    trackedStatus,
    totalInArea,
    kgrrCount: kgrrFlights.length,
    landedCount,
    lastUpdate: new Date().toISOString(),
    source: 'FR24+adsb.lol',
    error: null,
    weather
  };

  const trackedStr = trackedAirborne.length > 0 ? ` | tracked: ${trackedAirborne.map(f => f.registration).join(',')}` : '';
  const landedStr = landedCount > 0 ? ` | landed: ${landedCount}` : '';
  if (closest) {
    console.log(`[${ts()}] FR24:${fr24Flights.length} adsb:${adsbFlights.length} merged:${allByHome.length}${landedStr} | priority: ${priorityWithPhotos.length}${trackedStr} | closest: ${closest.flightNumber} ${closest.distHomeMi}mi`);
  } else {
    console.log(`[${ts()}] FR24:${fr24Flights.length} adsb:${adsbFlights.length} — no airborne flights`);
  }
}

function ts() { return new Date().toLocaleTimeString(); }

// ============================================
// Static File Server
// ============================================
const MIME = {
  '.html': 'text/html', '.css': 'text/css', '.js': 'application/javascript',
  '.json': 'application/json', '.png': 'image/png', '.svg': 'image/svg+xml', '.ico': 'image/x-icon',
};

function serveStatic(req, res) {
  const filePath = path.join(__dirname, 'public', req.url === '/' ? 'index.html' : req.url);
  fs.readFile(filePath, (err, data) => {
    if (err) { res.writeHead(404); res.end('Not Found'); }
    else {
      res.writeHead(200, { 'Content-Type': MIME[path.extname(filePath)] || 'application/octet-stream', 'Cache-Control': 'no-cache' });
      res.end(data);
    }
  });
}

// ============================================
// HTTP Server
// ============================================
http.createServer((req, res) => {
  res.setHeader('Access-Control-Allow-Origin', '*');

  if (req.url === '/api/flights') {
    res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
    res.end(JSON.stringify(flightData));
  } else if (req.url === '/api/weather') {
    res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
    res.end(JSON.stringify(flightData.weather));
  } else if (req.url.startsWith('/api/weather/')) {
    const icao = req.url.split('/api/weather/')[1].split('?')[0].toUpperCase();
    if (!icao || !/^[A-Z]{3,4}$/.test(icao)) {
      res.writeHead(400, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: 'Invalid ICAO code' }));
    } else {
      getWeather(icao).then(wx => {
        res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
        res.end(JSON.stringify(wx));
      }).catch(() => {
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify(null));
      });
    }
  } else if (req.url.startsWith('/api/atc-config')) {
    // /api/atc-config?icao=KXYZ — probe and return streams for a specific airport
    // /api/atc-config — return all known streams (for backward compat)
    const params = new URL(req.url, 'http://localhost').searchParams;
    const icao = (params.get('icao') || '').toUpperCase();
    if (icao && /^[A-Z]{3,4}$/.test(icao)) {
      getAtcStreams(icao).then(streams => {
        res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
        res.end(JSON.stringify({ [icao]: streams }));
      }).catch(() => {
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ [icao]: [] }));
      });
    } else {
      res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'public, max-age=300' });
      res.end(JSON.stringify(ATC_KNOWN));
    }
  } else if (req.url.startsWith('/api/atc/')) {
    // Route format: /api/atc/KGRR/tower
    const pathPart = req.url.split('/api/atc/')[1];
    const slashIdx = pathPart.indexOf('/');
    if (slashIdx === -1) { res.writeHead(404); res.end('Missing stream ID'); return; }
    const icao = pathPart.substring(0, slashIdx).toUpperCase();
    const streamId = pathPart.substring(slashIdx + 1);
    getAtcStreams(icao).then(streams => {
      const entry = streams.find(s => s.id === streamId);
      if (!entry) { res.writeHead(404); res.end('Unknown stream'); return; }
      const streamUrl = `http://d.liveatc.net/${entry.mount}`;
      function pipeStream(url) {
        const mod = url.startsWith('https') ? https : http;
        const streamReq = mod.get(url, { timeout: 10000 }, (streamRes) => {
          if (streamRes.statusCode >= 300 && streamRes.statusCode < 400 && streamRes.headers.location) {
            streamRes.resume();
            pipeStream(streamRes.headers.location);
            return;
          }
          if (streamRes.statusCode !== 200) {
            res.writeHead(502); res.end('Stream unavailable');
            streamRes.resume();
            return;
          }
          res.writeHead(200, {
            'Content-Type': 'audio/mpeg',
            'Cache-Control': 'no-store',
            'Transfer-Encoding': 'chunked'
          });
          streamRes.pipe(res);
          req.on('close', () => streamRes.destroy());
        });
        streamReq.on('error', () => { if (!res.headersSent) { res.writeHead(502); res.end('Stream error'); } });
        streamReq.on('timeout', () => { streamReq.destroy(); if (!res.headersSent) { res.writeHead(504); res.end('Stream timeout'); } });
      }
      pipeStream(streamUrl);
    }).catch(() => { res.writeHead(404); res.end('No ATC streams'); });
  } else if (req.url === '/api/flyins') {
    // Serve fly-in event data (static, from 2026 Michigan Fly-ins spreadsheet)
    res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'public, max-age=3600' });
    res.end(JSON.stringify({ airports: 45, events: 60, year: 2026, source: '2026 Michigan Fly-ins' }));
  } else if (req.url.startsWith('/api/photo/')) {
    const parts = req.url.split('/api/photo/')[1].split('?');
    const icao = parts[0];
    const params = new URLSearchParams(parts[1] || '');
    const reg = params.get('reg') || null;
    getPhoto(icao, reg).then(photo => {
      res.writeHead(200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify(photo));
    }).catch(() => {
      res.writeHead(200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify(null));
    });
  } else {
    serveStatic(req, res);
  }
}).listen(PORT, '0.0.0.0', () => {
  console.log(`\n  ✈  Flyover KGRR tracker v2`);
  console.log(`     http://0.0.0.0:${PORT}`);
  console.log(`     Home: ${HOME.lat}, ${HOME.lon}`);
  console.log(`     KGRR: ${KGRR.lat}, ${KGRR.lon}\n`);
  pollFlights();
  setInterval(pollFlights, POLL_INTERVAL);
});
