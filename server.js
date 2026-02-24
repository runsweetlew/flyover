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
// State & Caches
// ============================================
let flightData = {
  closest: null, flights: [], totalInArea: 0, kgrrCount: 0,
  lastUpdate: null, source: null, error: null, weather: null
};

// Track last time each flight's position changed (icao -> timestamp)
let lastPositionChange = {};
let lastPositions = {}; // icao -> {lat, lon}

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
async function getPhoto(icao) {
  if (!icao) return null;
  const hex = icao.toUpperCase();
  const cached = photoCache.get(hex);
  if (cached && Date.now() - cached.ts < PHOTO_TTL) return cached;

  try {
    const data = await fetchJSON(`https://api.planespotters.net/pub/photos/hex/${hex}`);
    if (data.photos && data.photos.length > 0) {
      const p = data.photos[0];
      const result = {
        url: p.thumbnail_large ? p.thumbnail_large.src : (p.thumbnail ? p.thumbnail.src : null),
        fullUrl: p.src || null,
        photographer: p.photographer || null,
        link: p.link || null,
        ts: Date.now()
      };
      photoCache.set(hex, result);
      return result;
    }
  } catch (err) {
    // Silently fail — photo is optional
  }
  const empty = { url: null, fullUrl: null, photographer: null, link: null, ts: Date.now() };
  photoCache.set(hex, empty);
  return empty;
}

// ============================================
// Weather Fetcher (aviationweather.gov METAR)
// ============================================
async function getWeather() {
  if (weatherCache.data && Date.now() - weatherCache.ts < WEATHER_TTL) {
    return weatherCache.data;
  }

  try {
    const data = await fetchJSON('https://aviationweather.gov/api/data/metar?ids=KGRR&format=json');
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

      weatherCache = { data: weather, ts: Date.now() };
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
    .filter(ac => ac.lat != null && ac.lon != null && ac.alt_baro !== 'ground')
    .map(ac => {
      const dHome = distanceMi(HOME.lat, HOME.lon, ac.lat, ac.lon);
      const dKGRR = distanceMi(KGRR.lat, KGRR.lon, ac.lat, ac.lon);
      const bHome = bearingDeg(HOME.lat, HOME.lon, ac.lat, ac.lon);
      const callsign = (ac.flight || '').trim();
      const airline = getAirline(callsign);
      const altFt = typeof ac.alt_baro === 'number' ? ac.alt_baro : (ac.alt_geom || null);
      const vertRate = ac.baro_rate || 0;
      const status = classifyFlight(dKGRR, altFt, vertRate);

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
        heading: ac.track != null ? Math.round(ac.track) : null,
        verticalRate: Math.round(vertRate),
        distHomeMi: Math.round(dHome * 10) / 10,
        distKGRRMi: Math.round(dKGRR * 10) / 10,
        bearingFromHome: Math.round(bHome),
        compassFromHome: compass(bHome),
        squawk: ac.squawk || null,
        status,
        isKGRR: status !== 'TRANSITING',
        isTracked: TRACKED_REGS.includes((ac.r || '').toUpperCase()),
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
// Poll Flight Data
// ============================================
async function pollFlights() {
  let flights = [];
  let source = null;
  let totalInArea = 0;

  // Expand search radius until we find at least one airborne flight
  let searchDist = SEARCH_DIST_NM;
  while (searchDist <= SEARCH_DIST_MAX_NM) {
    try {
      const data = await fetchJSON(`https://api.adsb.lol/v2/lat/${HOME.lat}/lon/${HOME.lon}/dist/${searchDist}`);
      flights = processAdsbLol(data.ac || []);
      totalInArea = (data.ac || []).length;
      source = 'adsb.lol';
      if (flights.length > 0) break;
      searchDist += SEARCH_DIST_STEP_NM;
    } catch (err) {
      console.error(`[${ts()}] adsb.lol failed at ${searchDist}nm: ${err.message}`);
      // Try OpenSky as fallback at base distance only
      try {
        const b = { lamin: HOME.lat - 0.72, lamax: HOME.lat + 0.72, lomin: HOME.lon - 1.0, lomax: HOME.lon + 1.0 };
        const data = await fetchJSON(`https://opensky-network.org/api/states/all?lamin=${b.lamin}&lamax=${b.lamax}&lomin=${b.lomin}&lomax=${b.lomax}`);
        flights = processOpenSky(data.states || []);
        totalInArea = (data.states || []).length;
        source = 'opensky';
      } catch (err2) {
        console.error(`[${ts()}] OpenSky also failed: ${err2.message}`);
        flightData = { ...flightData, error: 'Flight data APIs unavailable', lastUpdate: new Date().toISOString() };
        return;
      }
      break;
    }
  }

  // Fetch tracked planes individually (may be outside area search radius)
  if (source === 'adsb.lol') {
    const existingRegs = new Set(flights.map(f => f.registration).filter(Boolean));
    const missingRegs = TRACKED_REGS.filter(r => !existingRegs.has(r));
    if (missingRegs.length > 0) {
      const results = await Promise.all(missingRegs.map(reg =>
        fetchJSON(`https://api.adsb.lol/v2/reg/${reg}`).then(d => d.ac || []).catch(() => [])
      ));
      const extra = processAdsbLol(results.flat());
      const existingHex = new Set(flights.map(f => f.icao));
      extra.forEach(f => { if (!existingHex.has(f.icao)) flights.push(f); });
    }
    // Mark any flights already found in area search as tracked
    flights.forEach(f => { if (TRACKED_REGS.includes((f.registration || '').toUpperCase())) f.isTracked = true; });
  }

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

  // Closest is nearest plane to house, but skip:
  // 1. Landed planes (within 2mi of KGRR and below 500ft)
  // 2. Stale final planes (on final approach + no position update in 10s)
  let closest = null;
  for (const f of allByHome) {
    // KGRR field elevation ~794ft MSL — compute AGL
    const agl = f.altitudeFt != null ? f.altitudeFt - 794 : null;
    // Landed: near ground at KGRR, or very slow near KGRR (taxi/ground roll)
    const landed = (f.distKGRRMi < 2 && agl != null && agl < 200) ||
                   (f.distKGRRMi < 3 && f.speedKts != null && f.speedKts < 60);
    if (landed) continue;
    // Stale on final approach (no position update in 7s)
    const onFinal = f.status === 'ARRIVING' && f.distKGRRMi < 5 && agl != null && agl < 2200;
    const staleSec = (now - (lastPositionChange[f.icao] || now)) / 1000;
    if (onFinal && staleSec >= 7) continue;
    closest = f; break;
  }
  if (!closest) closest = allByHome[0] || null;

  // Build priority flights list:
  // - All airborne tracked planes
  // - Closest KGRR flight (first ARRIVING/DEPARTING by distance to KGRR)
  // If no tracked planes airborne, fall back to closest-to-home
  const trackedAirborne = allByHome.filter(f => f.isTracked);
  const closestKGRR = kgrrFlights.sort((a, b) => a.distKGRRMi - b.distKGRRMi)[0] || null;

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

  // Fetch photos for all priority flights
  const photoPromises = priorityFlights.map(async f => {
    const p = await getPhoto(f.icao);
    return { ...f, photo: p };
  });
  const priorityWithPhotos = await Promise.all(photoPromises);

  // Also fetch photo for closest (in case it's not in priority list)
  let closestPhoto = null;
  if (closest) {
    const existing = priorityWithPhotos.find(f => f.icao === closest.icao);
    closestPhoto = existing ? existing.photo : await getPhoto(closest.icao);
  }

  // Fetch weather (non-blocking)
  const weather = await getWeather();

  flightData = {
    closest: closest ? { ...closest, photo: closestPhoto } : null,
    priorityFlights: priorityWithPhotos,
    flights: allByHome,
    totalInArea,
    kgrrCount: kgrrFlights.length,
    lastUpdate: new Date().toISOString(),
    source,
    error: null,
    weather
  };

  const trackedStr = trackedAirborne.length > 0 ? ` | tracked: ${trackedAirborne.map(f => f.registration).join(',')}` : '';
  const distStr = searchDist > SEARCH_DIST_NM ? ` (${searchDist}nm)` : '';
  if (closest) {
    console.log(`[${ts()}] ${allByHome.length} aircraft${distStr} | priority: ${priorityWithPhotos.length}${trackedStr} | closest: ${closest.flightNumber} ${closest.distHomeMi}mi`);
  } else {
    console.log(`[${ts()}] No aircraft within ${searchDist}nm`);
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
  } else if (req.url.startsWith('/api/atc/')) {
    const stream = req.url.split('/api/atc/')[1];
    const mounts = { clearance:'kgrr2_2_del', ground:'kgrr2_2_gnd', tower:'kgrr2_2_twr', approach:'kgrr2_2_app' };
    const mount = mounts[stream];
    if (!mount) { res.writeHead(404); res.end('Unknown stream'); return; }
    const streamUrl = `http://d.liveatc.net/${mount}`;
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
  } else if (req.url.startsWith('/api/photo/')) {
    const icao = req.url.split('/api/photo/')[1];
    getPhoto(icao).then(photo => {
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
