
import * as THREE from "https://unpkg.com/three@0.165.0/build/three.module.js";
import { Line2 } from "https://unpkg.com/three@0.165.0/examples/jsm/lines/Line2.js";
import { LineGeometry } from "https://unpkg.com/three@0.165.0/examples/jsm/lines/LineGeometry.js";
import { LineMaterial } from "https://unpkg.com/three@0.165.0/examples/jsm/lines/LineMaterial.js";
import { mergeGeometries } from "https://unpkg.com/three@0.165.0/examples/jsm/utils/BufferGeometryUtils.js";

// Trips matching:  
// MOST INTERESTING! [march, april] = [41,42]
//                   [march, april] = [42,42]
//                   [march, april] = [48/49,48/49]
//
// 31 March:      AND       April 1: 
//    1                        16
//    7                         6
//    9                         7
//   10                         7
//   15                        13
//   22                        25
// 
// Almost / interesting: 
//
// 31 March:      AND       April 1: 
//    5                         3
//    6                         4

// WebXR AR support check
async function supportsAR() {
    if (!navigator.xr || !navigator.xr.isSessionSupported) return false;
    try {
    return await navigator.xr.isSessionSupported("immersive-ar");
    } catch {
    return false;
    }
}
// Initialize the AR session
(async function init() {
    // Get the buttons and elements
    const enterARButton = document.getElementById("enter-ar");
    const unsupportedEl = document.getElementById("unsupported");
    const placementToggleButton = document.getElementById("placement-toggle"); // Toggle placement mode
    const instructionsEl = document.getElementById("instructions"); // Instructions
    const centerReticleEl = document.getElementById("center-reticle"); // Center reticle
    const visibilityTogglesEl = document.getElementById("visibility-toggles");
    const toggleMapSurfaceBtn = document.getElementById("toggle-map-surface");
    const toggleRoadsBtn = document.getElementById("toggle-roads");
    const toggleGuideTimelinesBtn = document.getElementById("toggle-guide-timelines");
    const tapCaptureEl = document.getElementById("tap-capture");

    // Check if the browser/device supports AR
    if (!(await supportsAR())) {
    enterARButton.style.display = "none";
    unsupportedEl.style.display = "flex";
    return;
    }

    // Initialize the renderer, scene, and camera
    let renderer, scene, camera;
    let xrSession = null;
    let referenceSpace = null;
    let hitTestSource = null;
    let hitTestSourceRequested = false;
    let reticle = null;
    let placedPlane = null;
    let planeAnchor = null; // XRAnchor if available
    let planeOrientationOffset = null; // Align PlaneGeometry with detected surface
    let placementMode = true; // If false: no reticle + taps don't move plane
    let mapTexture = null; // Shared texture for reticle + placed plane
    let blockNextSelect = false; // Prevent UI taps from placing/moving plane

    const raycaster = new THREE.Raycaster();
    const rayCenter = new THREE.Vector2(0, 0);
    const lastViewerPosition = new THREE.Vector3();
    const lastViewerQuaternion = new THREE.Quaternion();
    const tmpReticleCorner = new THREE.Vector3();
    const tmpCamWorld = new THREE.Vector3();
    const tmpCamLocal = new THREE.Vector3();
    const tmpPlaneMatrixInv = new THREE.Matrix4();
    let tapMarkerMesh = null;
    let tapMarkerTwinMesh = null;
    const tmpHitLocal = new THREE.Vector3();
    const tmpTwinSpherePos = new THREE.Vector3();

    /** tap_trip_key -> pseudo-markers for nearest-point lookup (same heights as polylines) */
    const tapMarkersByTrip = new Map();
    let highlightedTripKey = null;

    // Event markers (one set per displayed path)
    const eventMarkers031 = [];
    const eventMarkers0401 = [];
    /** Built in rebuild when Compare duration is on; avoids O(n²) height work per vertex. */
    let compareHeightCache = null;
    const allEvents = []; // legacy, used for pointsOptions
    let eventsLoaded = false;
    let activeEventDate = null;
    let availableEventDates = [];

    // Trip data: [{ tripId, events }] for each file
    let trips3 = [];
    let trips4 = [];
    let currentTripIndex031 = 0;
    let currentTripIndex0401 = 0;
    let compareTripDuration = false;  // When true: long trip to 0.6m, short trip proportional (from 0.01m)
    // Display samples: ladder up to MAX_DISPLAY_SAMPLES; durations/compare use full trip.events (accurate).
    let pointsOptions = [100];
    let pointsToShowIndex = 0;
    /** Single merged road mesh geometry (built once in loadRoads). */
    let roadMergedGeometry = null;
    let roadsLoaded = false;
    /** In-flight load promises so preload + first placement never double-fetch. */
    let eventsLoadPromise = null;
    let roadsLoadPromise = null;

    let showMapSurface = true;
    let showGuideTimelines = false;
    let showRoads = true;

    function applyMapSurfaceVisibility() {
    if (!placedPlane?.material) return;
    placedPlane.material.opacity = showMapSurface ? 0.9 : 0;
    placedPlane.material.depthWrite = showMapSurface;
    }

    function applyGuideTimelinesVisibility() {
    const tl = placedPlane?.userData?.timeLinesGroup;
    if (tl) tl.visible = showGuideTimelines;
    }

    function applyRoadsVisibility() {
    const rg = placedPlane?.userData?.roadsGroup;
    if (rg) rg.visible = showRoads;
    }

    function applyOverlayUiVisibility() {
    const showOverlays = !!xrSession && !placementMode;
    if (visibilityTogglesEl) visibilityTogglesEl.style.display = showOverlays ? "flex" : "none";
    const tripDetailsEl = document.getElementById("trip-details");
    if (tripDetailsEl && !showOverlays) tripDetailsEl.classList.remove("visible");
    }

    /** Trip / points / compare controls only when browsing AR (not while aiming to place). */
    function syncBrowsePanelVisibility() {
    const show = eventsLoaded && !!xrSession && !placementMode;
    const tripEl = document.getElementById("trip-filter");
    const pointsEl = document.getElementById("event-date-filter");
    const compareBtn = document.getElementById("compare-duration-btn");
    if (tripEl) tripEl.style.display = show ? "flex" : "none";
    if (pointsEl) pointsEl.style.display = show ? "flex" : "none";
    if (compareBtn) compareBtn.style.display = show ? "block" : "none";
    }

    function disposeTapMarker() {
    const eg = placedPlane?.userData?.eventsGroup;
    if (tapMarkerMesh) {
        if (eg) eg.remove(tapMarkerMesh);
        tapMarkerMesh.geometry?.dispose();
        tapMarkerMesh.material?.dispose();
        tapMarkerMesh = null;
    }
    if (tapMarkerTwinMesh) {
        if (eg) eg.remove(tapMarkerTwinMesh);
        tapMarkerTwinMesh.geometry?.dispose();
        tapMarkerTwinMesh.material?.dispose();
        tapMarkerTwinMesh = null;
    }
    }

    function setPlacementMode(enabled) {
    placementMode = !!enabled;
    placementToggleButton.textContent = placementMode ? "Placement: ON" : "Placement: OFF";
    instructionsEl.textContent = placementMode
        ? "Placement mode: ON – move to find a surface, then tap to place a plane."
        : "Placement mode: OFF – walk around and observe the plane or explore dates.";
    if (!placementMode && reticle) reticle.visible = false;
    if (placementMode) {
        highlightedTripKey = null;
        disposeTapMarker();
        showTripDetails(null);
        applyTripHighlight();
    }
    applyOverlayUiVisibility();
    syncBrowsePanelVisibility();
    }

    if (toggleMapSurfaceBtn) toggleMapSurfaceBtn.classList.toggle("off", !showMapSurface);
    if (toggleRoadsBtn) toggleRoadsBtn.classList.toggle("off", !showRoads);
    if (toggleGuideTimelinesBtn) toggleGuideTimelinesBtn.classList.toggle("off", !showGuideTimelines);

    // Map image bounds in WGS84 (lat, lon). viscenter-norrkoping-map.png
    const mapCorners = {
    topLeft: [58.606672, 16.143959],
    topRight: [58.607120, 16.232280],
    bottomRight: [58.572833, 16.232774],
    bottomLeft: [58.572298, 16.144648]
    };

    // Same corners in EPSG:3006 (easting, northing, metres) — SWEREF 99 TM, for OSM GeoJSON.
    const MAP_SWEREF_EN_EXTENTS = {
    minE: 566469.0442700484,
    maxE: 571698.4256929675,
    minN: 6492996.223257078,
    maxN: 6496963.233584756
    };

    /** Roads GeoJSON (WGS84 or EPSG:3006). */
    const ROADS_GEOJSON_URL = "OSMroads-nkpg-new.geojson";

    const MAP_WIDTH = 3.2;
    const MAP_HEIGHT = 2.4;
    const MAP_HALF_X = MAP_WIDTH / 2;
    const MAP_HALF_Y = MAP_HEIGHT / 2;
    const ROAD_RIBBON_WIDTH = 0.004;

    /**
     * Max points used for AR geometry, tap polylines, and time→height along the drawn path.
     * Trip duration, compare wall times, and trip-details use full `trips3/4[].events` (not this cap).
     */
    const MAX_DISPLAY_SAMPLES = 200;

    /** Full event count on the limiting trip; not clamped (for UI denominator and mental model). */
    function getRawShorterTripEventCount() {
        const a = trips3[currentTripIndex031]?.events?.length ?? 0;
        const b = trips4[currentTripIndex0401]?.events?.length ?? 0;
        if (a > 0 && b > 0) return Math.min(a, b);
        return Math.max(a, b);
    }

    /** Cap for points UI and `eventMarkers*` sampling (performance). */
    function getDisplaySampleCap() {
        const raw = getRawShorterTripEventCount();
        return Math.min(Math.max(raw, 2), MAX_DISPLAY_SAMPLES);
    }

    const DEFAULT_POINTS_TARGET = 100;

    /** Steps ≤ cap (cap never exceeds MAX_DISPLAY_SAMPLES). */
    const POINTS_LADDER = [50, 100, 150, 200];
    function buildPointsOptions(cap) {
        const maxN = Math.max(2, Math.floor(cap));
        const set = new Set();
        for (const s of POINTS_LADDER) {
            if (s >= 2 && s <= maxN) set.add(s);
        }
        set.add(maxN);
        return [...set].sort((a, b) => a - b);
    }

    /**
     * Rebuild sample-count UI from current trip pair.
     * Default selection: min(100, cap) where cap is getDisplaySampleCap() (shorter trip, max 200).
     * Trip browsing passes preserveSelection=false so we always revert to that default.
     */
    function refreshPointsOptions(preserveSelection) {
        const cap = getDisplaySampleCap();
        const prevCount = preserveSelection ? pointsOptions[pointsToShowIndex] : null;
        pointsOptions = buildPointsOptions(cap);
        if (preserveSelection && prevCount != null) {
            const idx = pointsOptions.indexOf(prevCount);
            if (idx >= 0) {
                pointsToShowIndex = idx;
            } else if (prevCount > DEFAULT_POINTS_TARGET && pointsOptions.length > 1) {
                pointsToShowIndex = pointsOptions.length - 1;
            } else if (pointsOptions.includes(DEFAULT_POINTS_TARGET)) {
                pointsToShowIndex = pointsOptions.indexOf(DEFAULT_POINTS_TARGET);
            } else {
                pointsToShowIndex = pointsOptions.length - 1;
            }
        } else {
            const prefer = cap >= DEFAULT_POINTS_TARGET ? DEFAULT_POINTS_TARGET : cap;
            pointsToShowIndex = pointsOptions.indexOf(prefer);
            if (pointsToShowIndex < 0) pointsToShowIndex = pointsOptions.length - 1;
        }
        pointsToShowIndex = Math.max(0, Math.min(pointsToShowIndex, pointsOptions.length - 1));
        populatePointsFilter();
    }

    // "extract" "HH:MM" from "YYYY/MM/DD HH:MM:SS.sss" (for labels)
    function formatEventTime(dateTimeEvent) {
    if (!dateTimeEvent) return "";
    const part = dateTimeEvent.split(" ")[1];
    if (!part) return "";
    const [hms] = part.split(".");
    return hms ? hms.substring(0, 5) : part.substring(0, 5); // "HH:MM"
    }

    function formatEventDate(dateTimeEvent) {
    if (!dateTimeEvent) return "";
    const dateStr = dateTimeEvent.split(" ")[0]?.replace(/\//g, "-") || "";
    if (!dateStr) return "";
    const d = new Date(dateStr);
    if (isNaN(d.getTime())) return dateStr;
    const months = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
    return `${months[d.getMonth()]} ${d.getDate()}, ${d.getFullYear()}`;
    }

    function findClosestEventToHit(hitWorld, placedPlaneRef, markers) {
    if (!placedPlaneRef || !markers?.length) return null;
    const inv = new THREE.Matrix4().copy(placedPlaneRef.matrixWorld).invert();
    const hitLocal = new THREE.Vector3(hitWorld.x, hitWorld.y, hitWorld.z).applyMatrix4(inv);
    const maxDistSq = 0.55 * 0.55;
    let best = null;
    let bestDistSq = maxDistSq;
    for (const m of markers) {
        const x = m.userData?.localX;
        const y = m.userData?.localZ;
        const h = m.userData?.localH;
        if (x == null || y == null) continue;
        const dx = hitLocal.x - x;
        const dy = hitLocal.y - y;
        const dz = h == null ? 0 : (hitLocal.z - h);
        const d2 = dx * dx + dy * dy + dz * dz;
        if (d2 < bestDistSq) {
        bestDistSq = d2;
        best = m;
        }
    }
    return best;
    }

    function getLine2FromHitObject(obj) {
    let cur = obj;
    while (cur && !cur.isLine2 && cur.parent) cur = cur.parent;
    return cur?.isLine2 ? cur : null;
    }

    function findTapTripKeyFromHit(obj) {
    const line2 = getLine2FromHitObject(obj);
    if (!line2 || line2.userData?.tap_trip_key == null) return null;
    return String(line2.userData.tap_trip_key);
    }

    /** Same z as shadow FatLine in addEventsToPlane */
    const TRIP_SHADOW_Z = 0.01;

    /** Elevated polyline in plane space for tap key (matches drawPath heights). */
    function buildElevatedPolylineForTapKey(tapKey) {
    const colon = tapKey.indexOf(":");
    if (colon <= 0) return null;
    const sourceKey = tapKey.slice(0, colon);
    const markers = sourceKey === "04-01" ? eventMarkers0401 : eventMarkers031;
    if (!markers || markers.length < 2) return null;
    const tsSpanElev = compareTripDuration ? null : precomputeTimestampHeightSpan(markers);
    const getHeight = compareTripDuration
        ? (pt) => calculateHeightCompareDurations(eventMarkers031, eventMarkers0401, pt)
        : (pt) => timestampHeightFromSpan(tsSpanElev, pt);
    const out = [];
    for (const pt of markers) {
        out.push(new THREE.Vector3(pt.userData.localX, pt.userData.localZ, getHeight(pt)));
    }
    return out;
    }

    /** Closest point on polyline in XY; returns interpolated z on that segment. */
    function interpolateZAtXY(px, py, points) {
    if (!points || points.length < 2) return TRIP_SHADOW_Z;
    let bestD2 = Infinity;
    let bestZ = points[0].z;
    for (let i = 0; i < points.length - 1; i++) {
        const a = points[i];
        const b = points[i + 1];
        const vx = b.x - a.x;
        const vy = b.y - a.y;
        const wx = px - a.x;
        const wy = py - a.y;
        const len2 = vx * vx + vy * vy;
        const t = len2 < 1e-14 ? 0 : Math.max(0, Math.min(1, (wx * vx + wy * vy) / len2));
        const qx = a.x + t * vx;
        const qy = a.y + t * vy;
        const qz = a.z + t * (b.z - a.z);
        const d2 = (px - qx) * (px - qx) + (py - qy) * (py - qy);
        if (d2 < bestD2) {
        bestD2 = d2;
        bestZ = qz;
        }
    }
    return bestZ;
    }

    function applyTripHighlight() {
    const eventsGroup = placedPlane?.userData?.eventsGroup;
    if (!eventsGroup) return;
    eventsGroup.traverse((obj) => {
        if (!obj.isLine2 || !obj.material) return;
        const key = obj.userData?.tap_trip_key != null ? String(obj.userData.tap_trip_key) : null;
        if (!key) return;
        const baseWidth = obj.userData?.baseLinewidth ?? obj.material.linewidth ?? 0.01;
        const isShadow = (obj.name || "").startsWith("tripShadow");
        const selected = highlightedTripKey && key === highlightedTripKey;
        obj.material.transparent = true;
        if (obj.material.color) {
        if (!highlightedTripKey) {
            obj.material.color.setHex(0xffffff);
        } else if (selected) {
            obj.material.color.setHex(0xffffff);
        } else {
            obj.material.color.setHex(isShadow ? 0x14532d : 0x166534);
        }
        }
        if (isShadow) obj.position.z = highlightedTripKey && selected ? 0.004 : 0;
        obj.material.opacity = highlightedTripKey ? (selected ? 1 : 0.5) : 1;
        obj.material.linewidth = highlightedTripKey ? (selected ? baseWidth * 1.25 : baseWidth) : baseWidth;
        obj.material.needsUpdate = true;
    });
    }

    function dateTimeEventToMs(dt) {
        const d = new Date((dt || "").replace(/\//g, "-"));
        return isNaN(d.getTime()) ? null : d.getTime();
    }

    function wallDurationMsFromEvents(events) {
        if (!events || events.length < 2) return 0;
        const times = events.map((e) => dateTimeEventToMs(e.dateTimeEvent)).filter((t) => t != null);
        return times.length < 2 ? 0 : Math.max(...times) - Math.min(...times);
    }

    function formatTripDurationMs(ms) {
        if (ms <= 0 || !Number.isFinite(ms)) return "";
        const secTotal = Math.round(ms / 1000);
        if (secTotal < 60) return `${secTotal}s`;
        const minTotal = Math.floor(secTotal / 60);
        if (minTotal < 60) {
            const s = secTotal % 60;
            return s ? `${minTotal} min ${s}s` : `${minTotal} min`;
        }
        const h = Math.floor(minTotal / 60);
        const m = minTotal % 60;
        return m ? `${h} h ${m} min` : `${h} h`;
    }

    function findTripBySourceAndId(source, tripId) {
        const list = source === "03-31" ? trips3 : source === "04-01" ? trips4 : null;
        if (!list || tripId == null) return null;
        const key = String(tripId);
        return list.find((t) => String(t.tripId) === key) ?? null;
    }

    function showTripDetails(eventMarker) {
    const el = document.getElementById("trip-details");
    if (!el) return;
    if (!eventMarker?.userData) {
        el.classList.remove("visible");
        return;
    }
    const ud = eventMarker.userData;
    const trip = findTripBySourceAndId(ud.source, ud.trip_id);
    const durMs = trip ? wallDurationMsFromEvents(trip.events) : 0;
    const durStr = durMs > 0 ? formatTripDurationMs(durMs) : "";
    const src = ud.source === "04-01" ? "1 Apr" : ud.source === "03-31" ? "31 Mar" : (ud.source || "");
    const dateStr = formatEventDate(ud.dateTimeEvent);
    const timeStr = formatEventTime(ud.dateTimeEvent);
    const speedVal = typeof ud.speed_value === "number" ? ud.speed_value : null;
    const speedStr = speedVal != null ? ` · ${speedVal} m/s` : "";
    const durationPart = durStr ? ` · Trip duration: ${durStr}` : "";
    el.innerHTML = `<strong>${dateStr}</strong>${timeStr ? ` · ${timeStr}` : ""}${src ? ` · ${src}` : ""}${durationPart}${speedStr}`;
    el.classList.add("visible");
    }

    // Setup the three.js renderer, scene, and camera
    function setupThree() {
    renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
    renderer.setPixelRatio(window.devicePixelRatio);
    renderer.setSize(window.innerWidth, window.innerHeight);
    renderer.xr.enabled = true;
    renderer.domElement.style.width = "100%";
    renderer.domElement.style.height = "100%";
    document.body.appendChild(renderer.domElement);

    scene = new THREE.Scene();
    camera = new THREE.PerspectiveCamera(70, window.innerWidth / window.innerHeight, 0.01, 20);

    scene.add(new THREE.HemisphereLight(0xffffff, 0x444444, 1.0));
    const dirLight = new THREE.DirectionalLight(0xffffff, 0.7);
    dirLight.position.set(0.5, 1, 0.5);
    scene.add(dirLight);

    const textureLoader = new THREE.TextureLoader();
    textureLoader.load(
        "viscenter-norrkoping-map.png",
        (tex) => {
        tex.encoding = THREE.sRGBEncoding;
        tex.anisotropy = renderer.capabilities.getMaxAnisotropy();
        mapTexture = tex;
        if (reticle && reticle.material) { reticle.material.map = mapTexture; reticle.material.needsUpdate = true; }
        if (placedPlane && placedPlane.material) { placedPlane.material.map = mapTexture; placedPlane.material.needsUpdate = true; }
        },
        undefined,
        (err) => console.warn("Failed to load viscenter-norrkoping-map.png texture", err)
    );

    reticle = new THREE.Mesh(
        new THREE.PlaneGeometry(MAP_WIDTH, MAP_HEIGHT),
        new THREE.MeshBasicMaterial({
        color: 0xffffff,
        map: mapTexture || null,
        side: THREE.DoubleSide,
        transparent: true,
        opacity: 0.6
        })
    );
    reticle.visible = false;
    scene.add(reticle);

    planeOrientationOffset = new THREE.Quaternion().setFromEuler(
        new THREE.Euler(-Math.PI / 2, 0, 0)
    );

    window.addEventListener("resize", () => {
        camera.aspect = window.innerWidth / window.innerHeight;
        camera.updateProjectionMatrix();
        renderer.setSize(window.innerWidth, window.innerHeight);
        updateLineMaterialsResolution(placedPlane?.userData?.eventsGroup, renderer);
        updateLineMaterialsResolution(placedPlane?.userData?.roadsGroup, renderer);
    });
    }

    // Start the AR session
    async function startAR() {
    if (!renderer) setupThree();

    xrSession = await navigator.xr.requestSession("immersive-ar", {
        requiredFeatures: ["hit-test"],
        optionalFeatures: ["anchors", "local-floor", "dom-overlay"],
        domOverlay: { root: document.body }
    });

    xrSession.addEventListener("end", () => {
        xrSession = null;
        hitTestSourceRequested = false;
        hitTestSource = null;
        planeAnchor = null;
        // End the session
        if (renderer && renderer.xr) renderer.xr.setSession(null);

        enterARButton.style.display = "block";
        // Hide the buttons
        placementToggleButton.style.display = "none";
        centerReticleEl.style.display = "none";
        // Update the instructions
        instructionsEl.textContent = 'Tap "Enter AR" to start, then move your phone to find a surface.';
        highlightedTripKey = null;
        disposeTapMarker();
        showTripDetails(null);
        applyTripHighlight();
        if (tapCaptureEl) tapCaptureEl.style.display = "none";
        applyOverlayUiVisibility();
        syncBrowsePanelVisibility();
    });

    // Set the reference space type
    renderer.xr.setReferenceSpaceType("local-floor");
    // Set the session
    await renderer.xr.setSession(xrSession);
    referenceSpace = await xrSession.requestReferenceSpace("local-floor");

    // Request an animation frame
    xrSession.requestAnimationFrame(onXRFrame);

    // Show the buttons
    enterARButton.style.display = "none";
    placementToggleButton.style.display = "block";
    centerReticleEl.style.display = "block";

    setPlacementMode(true);

    // Preload + parse trips and roads while user aims — first tap only attaches meshes, not network/JSON.
    loadEvents().catch((err) => console.error("Preload trips failed:", err));
    loadRoads().catch((err) => console.error("Preload roads failed:", err));

    // On select event
    const onSelect = (event) => {
        if (blockNextSelect) { blockNextSelect = false; return; }

        const frame = event.frame;
        if (!frame || !referenceSpace) return;

        if (!placementMode) {
        runTapToInspect();
        return;
        }

        if (!hitTestSource) return;
        const hitTestResults = frame.getHitTestResults(hitTestSource);
        if (hitTestResults.length === 0) return;

        const hit = hitTestResults[0];
        const pose = hit.getPose(referenceSpace);
        if (!pose) return;

        if (xrSession.requestAnchor) {
            const planeQuat = new THREE.Quaternion(
                pose.transform.orientation.x, pose.transform.orientation.y,
                pose.transform.orientation.z, pose.transform.orientation.w
            ).multiply(planeOrientationOffset);
            const cornerToCenter = new THREE.Vector3(MAP_HALF_X, -MAP_HALF_Y, 0).applyQuaternion(planeQuat);
            const centerPos = {
                x: pose.transform.position.x + cornerToCenter.x,
                y: pose.transform.position.y + cornerToCenter.y,
                z: pose.transform.position.z + cornerToCenter.z
            };
            const anchorTransform = new XRRigidTransform(centerPos, {
                x: planeQuat.x, y: planeQuat.y, z: planeQuat.z, w: planeQuat.w
            });
            xrSession.requestAnchor(anchorTransform, referenceSpace)
            .then((anchor) => {
                planeAnchor = anchor;
                placeOrMovePlaneFromPose(pose);
                anchor.context = { threeObject: placedPlane };
                anchor.addEventListener("remove", () => { planeAnchor = null; });
                setPlacementMode(false);
            })
            .catch(() => {
                planeAnchor = null;
                placeOrMovePlaneFromPose(pose);
                setPlacementMode(false);
            });
        } else {
            planeAnchor = null;
            placeOrMovePlaneFromPose(pose);
            setPlacementMode(false);
        }
    };

    xrSession.addEventListener("select", onSelect);

    if (tapCaptureEl) tapCaptureEl.style.display = "block";
    }

    // Place or move the plane from the pose
    function placeOrMovePlaneFromPose(pose) {
    // Check if the plane is new
    const wasNewPlane = !placedPlane;

    if (!placedPlane) {
        const geometry = new THREE.PlaneGeometry(MAP_WIDTH, MAP_HEIGHT);
        // Create the plane material
        const material = new THREE.MeshStandardMaterial({
        color: 0xffffff,
        map: mapTexture || null,
        metalness: 0.1,
        roughness: 0.5,
        side: THREE.DoubleSide,
        transparent: true,
        opacity: 0.9
        });

        // Create the plane
        placedPlane = new THREE.Mesh(geometry, material);
        // Cast and receive shadows
        placedPlane.castShadow = true;
        placedPlane.receiveShadow = true;

        // Create the axes helper to see orientation of the plane
        const axesHelper = new THREE.AxesHelper(0.5);
        axesHelper.name = "planeDebugAxes";
        axesHelper.raycast = () => {};
        placedPlane.add(axesHelper);

        scene.add(placedPlane);
    }

    const { position, orientation } = pose.transform;
    if (planeOrientationOffset) {
        placedPlane.quaternion
        .set(orientation.x, orientation.y, orientation.z, orientation.w)
        .multiply(planeOrientationOffset);
    } else {
        placedPlane.quaternion.set(orientation.x, orientation.y, orientation.z, orientation.w);
    }
    const cornerToCenter = new THREE.Vector3(MAP_HALF_X, -MAP_HALF_Y, 0);
    cornerToCenter.applyQuaternion(placedPlane.quaternion);
    placedPlane.position.set(
        position.x + cornerToCenter.x,
        position.y + cornerToCenter.y,
        position.z + cornerToCenter.z
    );

    if (wasNewPlane) {
        Promise.all([loadEvents(), loadRoads()]).then(() => {
        if (!placedPlane) return;
        addEventsToPlane();
        addRoadsToPlane();
        });
    } else {
        if (eventMarkers031.length > 0 || eventMarkers0401.length > 0) addEventsToPlane();
        if (roadMergedGeometry) addRoadsToPlane();
    }
    applyMapSurfaceVisibility();
    }

    // XR frame loop: hit-test reticle, anchor updates, render
    function onXRFrame(time, frame) {
    const session = frame.session;
    session.requestAnimationFrame(onXRFrame);

    const pose = frame.getViewerPose(referenceSpace);
    if (!pose) return;
    const tv = pose.transform;
    lastViewerPosition.set(tv.position.x, tv.position.y, tv.position.z);
    lastViewerQuaternion.set(tv.orientation.x, tv.orientation.y, tv.orientation.z, tv.orientation.w);

    if (!hitTestSourceRequested) {
        session.requestReferenceSpace("viewer")
        .then((viewerSpace) => session.requestHitTestSource({ space: viewerSpace }))
        .then((source) => { hitTestSource = source; });
        hitTestSourceRequested = true;
    }

    // Check if the hit test source, reference space, reticle, and placement mode are valid
    if (hitTestSource && referenceSpace && reticle && placementMode) {
        // Get the hit test results
        const hitTestResults = frame.getHitTestResults(hitTestSource);
        if (hitTestResults.length > 0) {
        const hit = hitTestResults[0];
        const hitPose = hit.getPose(referenceSpace);
        if (hitPose) {
            const { position, orientation } = hitPose.transform;
            reticle.visible = true;
            if (planeOrientationOffset) {
            reticle.quaternion
                .set(orientation.x, orientation.y, orientation.z, orientation.w)
                .multiply(planeOrientationOffset);
            } else {
            reticle.quaternion.set(orientation.x, orientation.y, orientation.z, orientation.w);
            }
            tmpReticleCorner.set(MAP_HALF_X, -MAP_HALF_Y, 0);
            tmpReticleCorner.applyQuaternion(reticle.quaternion);
            reticle.position.set(position.x + tmpReticleCorner.x, position.y + tmpReticleCorner.y, position.z + tmpReticleCorner.z);
        }
        } else {
        reticle.visible = false;
        }
    }

    if (planeAnchor && placedPlane) {
        // Get the anchor pose
        const anchorPose = frame.getPose(
        planeAnchor.anchorSpace || planeAnchor.space || planeAnchor,
        referenceSpace
        );
        if (anchorPose) {
        const t = anchorPose.transform;
        placedPlane.position.set(t.position.x, t.position.y, t.position.z);

        if (planeOrientationOffset) {
            placedPlane.quaternion
            .set(t.orientation.x, t.orientation.y, t.orientation.z, t.orientation.w)
            .multiply(planeOrientationOffset);
        } else {
            placedPlane.quaternion.set(t.orientation.x, t.orientation.y, t.orientation.z, t.orientation.w);
        }
        }
    }

    // Move time-label sprites to the map edge furthest from the camera (full walk-around support)
    if (placedPlane && placedPlane.userData?.timeLinesGroup && camera) {
        camera.getWorldPosition(tmpCamWorld);

        // Camera position in plane-local space (X/Y edges, Z = height)
        tmpPlaneMatrixInv.copy(placedPlane.matrixWorld).invert();
        tmpCamLocal.copy(tmpCamWorld).applyMatrix4(tmpPlaneMatrixInv);

        const timeLinesGroup = placedPlane.userData.timeLinesGroup;

        // Count sprites first so we can spread them evenly along the chosen edge
        let spriteCount = 0;
        for (const child of timeLinesGroup.children) {
        if (child.isSprite) spriteCount++;
        }

        if (spriteCount > 0) {
        // Decide which edge is \"back\": horizontal (±Y) or vertical (±X)
        const useVerticalEdge = Math.abs(tmpCamLocal.x) >= Math.abs(tmpCamLocal.y);

        let spriteIndex = 0;
        for (const child of timeLinesGroup.children) {
            if (!child.isSprite) continue;

            const t = spriteCount === 1 ? 0.5 : spriteIndex / (spriteCount - 1);
            let x = 0;
            let y = 0;

            if (useVerticalEdge) {
            // Camera is more on +X / -X side → place labels on opposite X edge, spread along Y
            const edgeX = tmpCamLocal.x >= 0 ? -MAP_HALF_X : MAP_HALF_X;
            x = edgeX;
            y = -MAP_HALF_Y + t * (2 * MAP_HALF_Y);
            } else {
            // Camera is more on +Y / -Y side → place labels on opposite Y edge, spread along X
            const edgeY = tmpCamLocal.y >= 0 ? -MAP_HALF_Y : MAP_HALF_Y;
            y = edgeY;
            x = -MAP_HALF_X + t * (2 * MAP_HALF_X);
            }

            child.position.x = x;
            child.position.y = y;
            spriteIndex++;
        }
        }
    }

    renderer.render(scene, camera);
    }

    // Low speed (incl. 0) → black; higher speed → full trip hue so stops and slow legs read dark.
    function speedColorFromBlack(speed, maxSpeed, baseHex) {
        if (maxSpeed <= 0) return 0x000000;
        const t = Math.min(1, Math.max(0, speed / maxSpeed));
        const r0 = (baseHex >> 16) & 255;
        const g0 = (baseHex >> 8) & 255;
        const b0 = baseHex & 255;
        return (
            (Math.round(r0 * t) << 16) |
            (Math.round(g0 * t) << 8) |
            Math.round(b0 * t)
        );
    }

    // Line2/LineGeometry/LineMaterial for pathway (adopted from threejs.org/examples webgl_lines_fat)
    function createFatLinePathway(pathwayPoints, pointColors, lineWidth, parent, renderer, opts = {}) {
    if (!pathwayPoints || pathwayPoints.length < 2 || !pointColors) return null;

    const positions = [];
    const colors = [];

    for (let i = 0; i < pathwayPoints.length; i++) {
        const p = pathwayPoints[i];
        positions.push(p.x, p.y, p.z);
        const hex = pointColors[i] ?? 0x0088ff;
        colors.push(((hex >> 16) & 255) / 255, ((hex >> 8) & 255) / 255, (hex & 255) / 255);
    }
    const geometry = new LineGeometry();
    geometry.setPositions(positions);
    geometry.setColors(colors);
    const resolution = new THREE.Vector2();
    renderer.getSize(resolution);
    const matLine = new LineMaterial({
        color: 0xffffff,
        linewidth: lineWidth,
        vertexColors: true,
        dashed: false,
        alphaToCoverage: true,
        worldUnits: true,
        resolution
    });
    const line = new Line2(geometry, matLine);
    line.computeLineDistances();
    line.name = opts.name || "pathway";
    if (opts.renderOrder !== undefined) line.renderOrder = opts.renderOrder;
    if (opts.tapTripKey != null) {
        line.userData.tap_trip_key = opts.tapTripKey;
        line.userData.baseLinewidth = lineWidth;
    }
    parent.add(line);
    return line;
    }

    // Update LineMaterial resolution for all Line2 in a group (call on resize)
    function updateLineMaterialsResolution(group, renderer) {
    if (!group || !renderer) return;
    const resolution = new THREE.Vector2();
    renderer.getSize(resolution);
    group.traverse((obj) => {
        if (obj.isLine2 && obj.material && obj.material.resolution) {
        obj.material.resolution.copy(resolution);
        }
    });
    }

    // Five distinct colors for levelcomfort 1–5: red, orange, yellow, blue, green.
    function getComfortColor(level) {
        const i = Math.max(0, Math.min(4, Math.floor(level) - 1));
        const colors = [
            0xef4444, // 1 = red
            0xf97316, // 2 = orange
            0xeab308, // 3 = yellow
            0x3b82f6, // 4 = blue
            0x22c55e  // 5 = green
        ];
        return colors[i];
    }

    // Project WGS84 lat/lon -> plane local X/Z (meters), plane is MAP_WIDTH × MAP_HEIGHT centered at origin
    function projectToMapSurface(lat, lon) {
    const { topLeft, topRight, bottomLeft, bottomRight } = mapCorners;

    const minLat = Math.min(topLeft[0], topRight[0], bottomLeft[0], bottomRight[0]);
    const maxLat = Math.max(topLeft[0], topRight[0], bottomLeft[0], bottomRight[0]);
    const minLon = Math.min(topLeft[1], topRight[1], bottomLeft[1], bottomRight[1]);
    const maxLon = Math.max(topLeft[1], topRight[1], bottomLeft[1], bottomRight[1]);

    const normalizedLat = (lat - minLat) / (maxLat - minLat);
    const normalizedLon = (lon - minLon) / (maxLon - minLon);

    const x = (normalizedLon - 0.5) * MAP_WIDTH;
    const z = (normalizedLat - 0.5) * MAP_HEIGHT;
    return [x, z];
    }

    function projectSwerefToMapSurface(easting, northing) {
    const { minE, maxE, minN, maxN } = MAP_SWEREF_EN_EXTENTS;
    const normalizedLon = (easting - minE) / (maxE - minE);
    const normalizedLat = (northing - minN) / (maxN - minN);
    const x = (normalizedLon - 0.5) * MAP_WIDTH;
    const z = (normalizedLat - 0.5) * MAP_HEIGHT;
    return [x, z];
    }

    function geometryToRoadLineStrings(geometry) {
    if (!geometry?.coordinates) return [];
    if (geometry.type === "LineString") return [geometry.coordinates];
    if (geometry.type === "MultiLineString") return geometry.coordinates;
    return [];
    }

    function detectRoadsGeoCrs(geojson) {
    const urn = geojson.crs?.properties?.name || "";
    if (/EPSG::?4326\b/i.test(urn) || /CRS84/i.test(urn) || /WGS\s*84/i.test(urn)) return "CRS84";
    if (/EPSG::?3006\b/i.test(urn)) return "EPSG:3006";

    const f = geojson.features?.find((x) => geometryToRoadLineStrings(x.geometry).length);
    const lines = f ? geometryToRoadLineStrings(f.geometry) : [];
    const pt = lines[0]?.[0];
    if (!pt || pt.length < 2) return "CRS84";
    const a = Math.abs(pt[0]);
    const b = Math.abs(pt[1]);
    if (a > 1e5 && a < 2e6 && b > 5e6 && b < 8e6) return "EPSG:3006";
    return "CRS84";
    }

    function roadCoordToPlaneXZ(coord, crs) {
    if (crs === "EPSG:3006") {
        const [easting, northing] = coord;
        return projectSwerefToMapSurface(easting, northing);
    }
    const lon = coord[0];
    const lat = coord[1];
    return projectToMapSurface(lat, lon);
    }

    // Parse GeoJSON features into trips grouped by trip_id (use String for large IDs)
    function parseGeojsonToTrips(geojson, source) {
        if (!geojson?.features || !Array.isArray(geojson.features)) return [];
        const byTrip = new Map();
        for (const f of geojson.features) {
            const tid = f.properties?.trip_id;
            if (tid == null) continue;
            const key = String(tid);
            if (!byTrip.has(key)) byTrip.set(key, []);
            byTrip.get(key).push(f);
        }
        const trips = [];
        for (const [tripId, features] of byTrip) {
            const sorted = features.sort((a, b) => {
                const tA = new Date((a.properties?.time || "").replace(/\//g, "-")).getTime();
                const tB = new Date((b.properties?.time || "").replace(/\//g, "-")).getTime();
                return tA - tB;
            });
            const events = [];
            for (const feature of sorted) {
                const props = feature.properties || {};
                const dateTimeEvent = props.time;
                const coords = feature.geometry?.coordinates;
                if (!dateTimeEvent || !coords || coords.length < 2) continue;
                const lon = coords[0], lat = coords[1];
                if (isNaN(lon) || isNaN(lat)) continue;
                const [x, z] = projectToMapSurface(lat, lon);
                events.push({
                    id: props.entity_id || "",
                    dateTimeEvent,
                    date: "trip",
                    source,
                    trip_id: tripId,
                    lat, lon,
                    levelcomfort: 4,
                    localX: x,
                    localZ: z,
                    speed_value: typeof props.speed_value === "number" ? props.speed_value : 0
                });
            }
            if (events.length >= 2) trips.push({ tripId, events });
        }
        trips.sort((a, b) => String(a.tripId).localeCompare(String(b.tripId)));
        return trips;
    }

    function loadEvents() {
    if (eventsLoaded) return Promise.resolve();
    if (eventsLoadPromise) return eventsLoadPromise;
    eventsLoadPromise = (async () => {
        try {
        const [r031, r0401] = await Promise.all([
            fetch("bus_data_trim_03-31.geojson"),
            fetch("bus_data_trim_04-01.geojson")
        ]);
        const [gj031, gj0401] = await Promise.all([r031.json(), r0401.json()]);
        trips3 = parseGeojsonToTrips(gj031, "03-31");
        trips4 = parseGeojsonToTrips(gj0401, "04-01");

        eventsLoaded = true;
        activeEventDate = "trip";
        currentTripIndex031 = Math.min(currentTripIndex031, Math.max(0, trips3.length - 1));
        currentTripIndex0401 = Math.min(currentTripIndex0401, Math.max(0, trips4.length - 1));
        refreshPointsOptions(false);
        populateTripFilter();
        rebuildEventMarkersForActiveDate();
        } catch (err) {
        console.error("Failed to load bus trips:", err);
        } finally {
        eventsLoadPromise = null;
        }
    })();
    return eventsLoadPromise;
    }

    // Sample indices: always first and last, evenly spaced in between
    function getSampledIndices(total, targetCount) {
    if (targetCount >= total) return [...Array(total).keys()];
    if (targetCount <= 2) return [0, total - 1];
    const indices = new Set([0, total - 1]);
    for (let i = 1; i < targetCount - 1; i++) {
        const t = i / (targetCount - 1);
        indices.add(Math.round(t * (total - 1)));
    }
    return [...indices].sort((a, b) => a - b);
    }

    // Recreate event markers for both trips at currentTripIndex (03-31 + 04-01)
    function rebuildEventMarkersForActiveDate() {
    eventMarkers031.length = 0;
    eventMarkers0401.length = 0;

    if (!activeEventDate) return;

    const trip031 = trips3[currentTripIndex031];
    const trip0401 = trips4[currentTripIndex0401];

    function sampleAndPush(events, out) {
        if (!events || events.length === 0) return;
        const targetCount = Math.min(pointsOptions[pointsToShowIndex] ?? DEFAULT_POINTS_TARGET, events.length);
        const indices = getSampledIndices(events.length, targetCount);
        for (const idx of indices) {
            const ev = events[idx];
            out.push({ userData: { ...ev, isEventMarker: true } });
        }
    }

    if (trip031) sampleAndPush(trip031.events, eventMarkers031);
    if (trip0401) sampleAndPush(trip0401.events, eventMarkers0401);

    compareHeightCache = compareTripDuration
        ? buildCompareHeightCache(eventMarkers031, eventMarkers0401)
        : null;

    buildTapInspectMarkers();

    if (placedPlane && placedPlane.userData?.eventsGroup) addEventsToPlane();
    updatePointsLabel();
    updateTripLabels();
    }

    const H_TIMESTAMP_MIN = 0.05;
    const H_TIMESTAMP_MAX = 0.5;
    const H_COMPARE_MAX = 0.6;
    const H_COMPARE_MIN = 0.01;

    /** One pass over sampled markers for min/max event time (used for per-vertex height). */
    function precomputeTimestampHeightSpan(markers) {
        if (!markers || markers.length <= 1) return { degenerate: true };
        let minT = Infinity;
        let maxT = -Infinity;
        for (let i = 0; i < markers.length; i++) {
            const t = dateTimeEventToMs(markers[i].userData?.dateTimeEvent);
            if (t == null) continue;
            if (t < minT) minT = t;
            if (t > maxT) maxT = t;
        }
        if (!Number.isFinite(minT) || minT >= maxT) return { degenerate: true };
        return { minT, maxT, span: maxT - minT || 1 };
    }

    function timestampHeightFromSpan(span, markerLike) {
        if (!span || span.degenerate) return H_TIMESTAMP_MIN;
        const ud = markerLike.userData ?? markerLike;
        const t = dateTimeEventToMs(ud.dateTimeEvent);
        if (t == null) return H_TIMESTAMP_MIN;
        const normalized = (t - span.minT) / span.span;
        return H_TIMESTAMP_MIN + normalized * (H_TIMESTAMP_MAX - H_TIMESTAMP_MIN);
    }

    // Timestamp -> height along trip: 0.05m (start) .. 0.5m (end); degenerate cases → 0.05m.
    function calculateHeightFromTimestamp(eventMarkers, targetMarker) {
        const span = precomputeTimestampHeightSpan(eventMarkers);
        return timestampHeightFromSpan(span, targetMarker);
    }

    function buildCompareHeightCache(markers031, markers0401) {
        const trip03 = trips3[currentTripIndex031];
        const trip04 = trips4[currentTripIndex0401];
        const dur031 = trip03 ? wallDurationMsFromEvents(trip03.events) : 0;
        const dur0401 = trip04 ? wallDurationMsFromEvents(trip04.events) : 0;
        const durationShort = Math.min(dur031 || dur0401, dur0401 || dur031) || 1;
        const durationLong = Math.max(dur031 || 0, dur0401 || 0) || 1;
        const hEndShort = Math.max(H_COMPARE_MIN, H_COMPARE_MAX * (durationShort / durationLong));
        return {
            dur031,
            dur0401,
            durationLong,
            hEndLong: H_COMPARE_MAX,
            hEndShort,
            span031: precomputeTimestampHeightSpan(markers031),
            span0401: precomputeTimestampHeightSpan(markers0401)
        };
    }

    // Uses compareHeightCache (built once per marker rebuild) so each vertex is O(1).
    function calculateHeightCompareDurations(markers031, markers0401, targetMarker) {
        let c = compareHeightCache;
        if (!c) {
            c = buildCompareHeightCache(markers031, markers0401);
            compareHeightCache = c;
        }
        const src = targetMarker.userData?.source;
        const span = src === "03-31" ? c.span031 : c.span0401;
        const durThis = src === "03-31" ? c.dur031 : c.dur0401;
        if (!span || span.degenerate) return H_COMPARE_MIN;
        const targetT = dateTimeEventToMs(targetMarker.userData.dateTimeEvent);
        if (targetT == null) return H_COMPARE_MIN;
        const norm = (targetT - span.minT) / span.span;
        const isLongTrip = durThis + 0.5 >= c.durationLong;
        const hEnd = isLongTrip ? c.hEndLong : c.hEndShort;
        return H_COMPARE_MIN + norm * (hEnd - H_COMPARE_MIN);
    }

    function buildTapInspectMarkers() {
        tapMarkersByTrip.clear();
        function ingest(markers, sourceKey) {
        if (!markers || markers.length < 2) return;
        const tripId = markers[0].userData?.trip_id;
        if (tripId == null) return;
        const tapKey = `${sourceKey}:${tripId}`;
        const tsSpan = compareTripDuration ? null : precomputeTimestampHeightSpan(markers);
        const arr = [];
        for (const m of markers) {
            const localH = compareTripDuration
                ? calculateHeightCompareDurations(eventMarkers031, eventMarkers0401, m)
                : timestampHeightFromSpan(tsSpan, m);
            arr.push({
            userData: {
                ...m.userData,
                trip_id: tripId,
                source: sourceKey,
                localH,
                isEventMarker: true
            }
            });
        }
        tapMarkersByTrip.set(tapKey, arr);
        }
        ingest(eventMarkers031, "03-31");
        ingest(eventMarkers0401, "04-01");
    }

    function runTapToInspect() {
        if (!placedPlane || placementMode) return;
        camera.position.copy(lastViewerPosition);
        camera.quaternion.copy(lastViewerQuaternion);
        camera.updateMatrixWorld(true);
        raycaster.setFromCamera(rayCenter, camera);
        const eventsGroup = placedPlane.userData?.eventsGroup;
        const pickTargets = eventsGroup ? [eventsGroup, placedPlane] : [placedPlane];
        const intersects = raycaster.intersectObjects(pickTargets, true);
        const hitPoint = intersects.length > 0 ? intersects[0].point : null;
        const hitObject = intersects.length > 0 ? intersects[0].object : null;
        const tripKeyFromHit = hitObject ? findTapTripKeyFromHit(hitObject) : null;
        if (!tripKeyFromHit) {
        highlightedTripKey = null;
        applyTripHighlight();
        showTripDetails(null);
        disposeTapMarker();
        return;
        }
        highlightedTripKey = tripKeyFromHit;
        applyTripHighlight();
        const markersForTrip = tapMarkersByTrip.get(tripKeyFromHit) || [];
        const closest = hitPoint ? findClosestEventToHit(hitPoint, placedPlane, markersForTrip) : null;
        showTripDetails(closest);
        if (eventsGroup) {
        disposeTapMarker();
        if (hitPoint) {
            const inv = new THREE.Matrix4().copy(placedPlane.matrixWorld).invert();
            tmpHitLocal.copy(hitPoint).applyMatrix4(inv);
            const line2Hit = getLine2FromHitObject(hitObject);
            const hitShadow = !!(line2Hit && (line2Hit.name || "").startsWith("tripShadow"));
            const elevatedPoly = buildElevatedPolylineForTapKey(tripKeyFromHit);

            const geomPrimary = new THREE.SphereGeometry(0.012, 16, 12);
            const matPrimary = new THREE.MeshBasicMaterial({ color: 0xffff00 });
            tapMarkerMesh = new THREE.Mesh(geomPrimary, matPrimary);
            tapMarkerMesh.position.copy(tmpHitLocal);
            tapMarkerMesh.renderOrder = 10;
            eventsGroup.add(tapMarkerMesh);

            const canTwinFromShadow = hitShadow && elevatedPoly && elevatedPoly.length >= 2;
            const canTwinFromElevated = !hitShadow;
            if (canTwinFromShadow || canTwinFromElevated) {
            const geomTwin = new THREE.SphereGeometry(0.011, 14, 10);
            const matTwin = new THREE.MeshBasicMaterial({ color: 0x22d3ee });
            tapMarkerTwinMesh = new THREE.Mesh(geomTwin, matTwin);
            tapMarkerTwinMesh.renderOrder = 11;
            if (hitShadow) {
                const zElev = interpolateZAtXY(tmpHitLocal.x, tmpHitLocal.y, elevatedPoly);
                tmpTwinSpherePos.set(tmpHitLocal.x, tmpHitLocal.y, zElev);
            } else {
                tmpTwinSpherePos.set(tmpHitLocal.x, tmpHitLocal.y, TRIP_SHADOW_Z);
            }
            tapMarkerTwinMesh.position.copy(tmpTwinSpherePos);
            eventsGroup.add(tapMarkerTwinMesh);
            }
        }
        }
    }

    // Add markers as children of the plane (draw two paths: 03-31 blue, 04-01 orange)
    function addEventsToPlane() {
    const hasAny = eventMarkers031.length > 0 || eventMarkers0401.length > 0;
    if (!placedPlane || !hasAny) return;

    disposeTapMarker();

    if (!placedPlane.userData.eventsGroup) {
        const eventsGroup = new THREE.Group();
        eventsGroup.name = "eventsGroup";
        eventsGroup.rotation.y = 0;
        placedPlane.add(eventsGroup);
        placedPlane.userData.eventsGroup = eventsGroup;
    }

    const eventsGroup = placedPlane.userData.eventsGroup;
    if (!eventsGroup) return;

    // Dispose and remove previous height-lines group
    const prevTimeLines = placedPlane.userData.timeLinesGroup;
    if (prevTimeLines) {
        prevTimeLines.traverse((o) => {
            if (o.geometry) o.geometry.dispose();
            if (o.material) {
                if (o.material.map && o.material.map.dispose) o.material.map.dispose();
                o.material.dispose();
            }
        });
        eventsGroup.remove(prevTimeLines);
        placedPlane.userData.timeLinesGroup = null;
    }

    // Dispose previous children (e.g. trip lines)
    while (eventsGroup.children.length) {
        const child = eventsGroup.children[0];
        eventsGroup.remove(child);
        if (child.geometry) child.geometry.dispose();
        if (child.material) child.material.dispose();
    }

    // Draw path for each source (03-31 = blue tint, 04-01 = orange tint)
    const COLOR_031 = 0x0088ff;  // blue
    const COLOR_0401 = 0xf97316;  // orange
    function drawPath(markers, baseColor, sourceKey) {
        if (!markers || markers.length < 2) return;
        const tid = markers[0].userData?.trip_id;
        const tapTripKey = tid != null ? `${sourceKey}:${tid}` : null;
        const linePoints = [];
        let maxSpeed = 0;
        const tsSpanPath = compareTripDuration ? null : precomputeTimestampHeightSpan(markers);
        const getHeight = compareTripDuration
            ? (pt) => calculateHeightCompareDurations(eventMarkers031, eventMarkers0401, pt)
            : (pt) => timestampHeightFromSpan(tsSpanPath, pt);
        for (const pt of markers) {
            const speed = pt.userData.speed_value ?? 0;
            if (speed > maxSpeed) maxSpeed = speed;
            const height = getHeight(pt);
            linePoints.push(new THREE.Vector3(pt.userData.localX, pt.userData.localZ, height));
        }
        const pointColors = markers.map((pt) =>
            speedColorFromBlack(pt.userData.speed_value ?? 0, maxSpeed, baseColor)
        );
        if (renderer) {
            const lineOpts = { name: "tripLine", renderOrder: 0, tapTripKey };
            const shadowOpts = { name: "tripShadow", renderOrder: -1, tapTripKey };
            createFatLinePathway(linePoints, pointColors, 0.01, eventsGroup, renderer, lineOpts);
            const shadowPoints = linePoints.map((p) => new THREE.Vector3(p.x, p.y, TRIP_SHADOW_Z));
            createFatLinePathway(shadowPoints, pointColors, 0.01, eventsGroup, renderer, shadowOpts);
        }
    }
    drawPath(eventMarkers031, COLOR_031, "03-31");
    drawPath(eventMarkers0401, COLOR_0401, "04-01");

    // Time labels: use 03-31 if available, else 04-01
    let primaryMarkers = eventMarkers031.length >= 2 ? eventMarkers031 : eventMarkers0401;
    if (primaryMarkers.length < 2) primaryMarkers = [];
    const firstMarker = primaryMarkers[0];
    const lastMarker = primaryMarkers[primaryMarkers.length - 1];
    const tsSpanPrimary = compareTripDuration ? null : precomputeTimestampHeightSpan(primaryMarkers);
    const getH = compareTripDuration
        ? (m) => calculateHeightCompareDurations(eventMarkers031, eventMarkers0401, m)
        : (m) => timestampHeightFromSpan(tsSpanPrimary, m);
    const hFirst = firstMarker ? getH(firstMarker) : 0.05;
    const hLast = lastMarker ? getH(lastMarker) : 0.05;
    const heights = [hFirst, hLast];
    const timeLabels = firstMarker && lastMarker
        ? [formatEventTime(firstMarker.userData.dateTimeEvent), formatEventTime(lastMarker.userData.dateTimeEvent)]
        : ["—", "—"];

    const timeLinesGroup = new THREE.Group();
    timeLinesGroup.name = "timeLinesGroup";
    const contourRibbonWidth = 0.01; // thick line (5x for 2m map)
    const contourMaterial = new THREE.MeshBasicMaterial({ color: 0x444444, side: THREE.DoubleSide });

    const nHeights = heights.length;
    for (let i = 0; i < nHeights; i++) {
        const h = heights[i];
        const points = [
            new THREE.Vector3(-MAP_HALF_X, -MAP_HALF_Y, h),
            new THREE.Vector3(MAP_HALF_X, -MAP_HALF_Y, h),
            new THREE.Vector3(MAP_HALF_X, MAP_HALF_Y, h),
            new THREE.Vector3(-MAP_HALF_X, MAP_HALF_Y, h),
            new THREE.Vector3(-MAP_HALF_X, -MAP_HALF_Y, h)
        ];
        const ribbonGeom = createRibbonGeometry(points, contourRibbonWidth);
        if (ribbonGeom) {
            const ribbon = new THREE.Mesh(ribbonGeom, contourMaterial);
            timeLinesGroup.add(ribbon);
        }

        const timeStr = timeLabels[i] || "";
        if (!timeStr) continue;
        // create a canvas for the time label
        const canvas = document.createElement("canvas");
        const ctx = canvas.getContext("2d");
        const w = 128;
        canvas.width = w;
        canvas.height = 48;
        ctx.fillStyle = "rgba(0,0,0,0.7)";
        ctx.fillRect(0, 0, w, 48);
        ctx.fillStyle = "#fff";
        ctx.font = "bold 24px system-ui, sans-serif";
        ctx.textAlign = "center";
        ctx.fillText(timeStr, w / 2, 30);
        // create a texture from the canvas
        const tex = new THREE.CanvasTexture(canvas);
        // force texture update
        tex.needsUpdate = true;
        const spriteMat = new THREE.SpriteMaterial({ map: tex, transparent: true });
        const sprite = new THREE.Sprite(spriteMat);
        const labelX = nHeights <= 1 ? 0 : -MAP_HALF_X + (i / (nHeights - 1)) * (2 * MAP_HALF_X);
        sprite.position.set(labelX, MAP_HALF_Y, h);
        sprite.scale.set(0.2, 0.1, 1);
        timeLinesGroup.add(sprite);
    }
    // store a reference to the time lines group in placedPlane.userData
    placedPlane.userData.timeLinesGroup = timeLinesGroup;
    // make timeLinesGroup visible in the scene graph + moves with the plane
    eventsGroup.add(timeLinesGroup);
    applyGuideTimelinesVisibility();
    applyTripHighlight();
    }

    function removeEventsFromPlane() {
    const eventsGroup = placedPlane?.userData?.eventsGroup;
    if (eventsGroup) placedPlane.userData.eventsGroup = null;
    }

    // Build a flat ribbon strip along points (for thick road lines)
    // Optional depth: extrude in Z for vertical thickness (e.g. trip line)
    function createRibbonGeometry(points, width, depth = 0, computeNormals = true) {
    if (!points || points.length < 2) return null;

    const halfWidth = width / 2;
    const halfDepth = depth / 2;
    const positions = [];
    const indices = [];
    const eps = 1e-6;
    let lastPerp = null; // reuse when segment is vertical (same lat/lon, different time)

    for (let i = 0; i < points.length - 1; i++) {
        const p1 = points[i];
        const p2 = points[i + 1];

        const dir = new THREE.Vector3().subVectors(p2, p1).normalize();
        let perp = new THREE.Vector3(-dir.y, dir.x, 0).multiplyScalar(halfWidth);
        if (perp.length() < eps) {
        // Vertical segment (bus stopped: same location, different height) – use previous perp, no subdivision
        perp = lastPerp ? lastPerp.clone() : new THREE.Vector3(halfWidth, 0, 0);
        } else {
        lastPerp = perp.clone();
        }

        const v1 = new THREE.Vector3().addVectors(p1, perp);
        const v2 = new THREE.Vector3().subVectors(p1, perp);
        const v3 = new THREE.Vector3().addVectors(p2, perp);
        const v4 = new THREE.Vector3().subVectors(p2, perp);

        const baseIndex = positions.length / 3;

        if (depth > 0) {
        // Extruded ribbon: top and bottom faces, plus 4 sides
        const top = (v, z) => [v.x, v.y, v.z + z];
        const bot = (v, z) => [v.x, v.y, v.z - z];
        positions.push(
            ...top(v1, halfDepth), ...top(v2, halfDepth), ...top(v3, halfDepth), ...top(v4, halfDepth),
            ...bot(v1, halfDepth), ...bot(v2, halfDepth), ...bot(v3, halfDepth), ...bot(v4, halfDepth)
        );
        // Top, bottom, 4 sides (full box per segment)
        indices.push(
            baseIndex, baseIndex + 1, baseIndex + 2, baseIndex + 1, baseIndex + 3, baseIndex + 2,
            baseIndex + 4, baseIndex + 6, baseIndex + 5, baseIndex + 5, baseIndex + 6, baseIndex + 7,
            baseIndex, baseIndex + 4, baseIndex + 5, baseIndex, baseIndex + 5, baseIndex + 1,
            baseIndex + 1, baseIndex + 5, baseIndex + 6, baseIndex + 1, baseIndex + 6, baseIndex + 2,
            baseIndex + 2, baseIndex + 6, baseIndex + 7, baseIndex + 2, baseIndex + 7, baseIndex + 3,
            baseIndex + 3, baseIndex + 7, baseIndex + 4, baseIndex + 3, baseIndex + 4, baseIndex
        );
        } else {
        positions.push(
            v1.x, v1.y, v1.z, v2.x, v2.y, v2.z, v3.x, v3.y, v3.z, v4.x, v4.y, v4.z
        );
        indices.push(
            baseIndex, baseIndex + 1, baseIndex + 2, baseIndex + 1, baseIndex + 3, baseIndex + 2
        );
        }
    }

    const geometry = new THREE.BufferGeometry();
    geometry.setAttribute("position", new THREE.Float32BufferAttribute(positions, 3));
    geometry.setIndex(indices);
    if (computeNormals) geometry.computeVertexNormals();
    return geometry;
    }

    // Trip ribbon with vertex colors interpolated between points (preserves stops, no fake points)
    function createTripRibbonGeometry(points, pointColors, width, depth = 0) {
    if (!points || points.length < 2 || !pointColors || pointColors.length !== points.length) return null;

    const halfWidth = width / 2;
    const halfDepth = depth / 2;
    const positions = [];
    const colors = [];
    const indices = [];
    const eps = 1e-6;
    let lastPerp = null;

    const toRGB = (hex) => {
        const r = ((hex >> 16) & 255) / 255;
        const g = ((hex >> 8) & 255) / 255;
        const b = (hex & 255) / 255;
        return [r, g, b];
    };

    for (let i = 0; i < points.length - 1; i++) {
        const p1 = points[i];
        const p2 = points[i + 1];
        const c1 = toRGB(pointColors[i]);
        const c2 = toRGB(pointColors[i + 1]);

        const dir = new THREE.Vector3().subVectors(p2, p1).normalize();
        let perp = new THREE.Vector3(-dir.y, dir.x, 0).multiplyScalar(halfWidth);
        if (perp.length() < eps) {
        perp = lastPerp ? lastPerp.clone() : new THREE.Vector3(halfWidth, 0, 0);
        } else {
        lastPerp = perp.clone();
        }

        const v1 = new THREE.Vector3().addVectors(p1, perp);
        const v2 = new THREE.Vector3().subVectors(p1, perp);
        const v3 = new THREE.Vector3().addVectors(p2, perp);
        const v4 = new THREE.Vector3().subVectors(p2, perp);

        const baseIndex = positions.length / 3;

        if (depth > 0) {
        // Extruded box per segment: top, bottom, 4 sides
        const top = (v, z) => [v.x, v.y, v.z + z];
        const bot = (v, z) => [v.x, v.y, v.z - z];
        positions.push(
            ...top(v1, halfDepth), ...top(v2, halfDepth), ...top(v3, halfDepth), ...top(v4, halfDepth),
            ...bot(v1, halfDepth), ...bot(v2, halfDepth), ...bot(v3, halfDepth), ...bot(v4, halfDepth)
        );
        colors.push(...c1, ...c1, ...c2, ...c2, ...c1, ...c1, ...c2, ...c2);
        // Top, bottom, 4 sides (full box per segment)
        indices.push(
            baseIndex, baseIndex + 1, baseIndex + 2, baseIndex + 1, baseIndex + 3, baseIndex + 2,
            baseIndex + 4, baseIndex + 6, baseIndex + 5, baseIndex + 5, baseIndex + 6, baseIndex + 7,
            baseIndex, baseIndex + 4, baseIndex + 5, baseIndex, baseIndex + 5, baseIndex + 1,
            baseIndex + 1, baseIndex + 5, baseIndex + 6, baseIndex + 1, baseIndex + 6, baseIndex + 2,
            baseIndex + 2, baseIndex + 6, baseIndex + 7, baseIndex + 2, baseIndex + 7, baseIndex + 3,
            baseIndex + 3, baseIndex + 7, baseIndex + 4, baseIndex + 3, baseIndex + 4, baseIndex
        );
        } else {
        positions.push(v1.x, v1.y, v1.z, v2.x, v2.y, v2.z, v3.x, v3.y, v3.z, v4.x, v4.y, v4.z);
        colors.push(...c1, ...c1, ...c2, ...c2);
        indices.push(baseIndex, baseIndex + 1, baseIndex + 2, baseIndex + 1, baseIndex + 3, baseIndex + 2);
        }
    }

    const geometry = new THREE.BufferGeometry();
    geometry.setAttribute("position", new THREE.Float32BufferAttribute(positions, 3));
    geometry.setAttribute("color", new THREE.Float32BufferAttribute(colors, 3));
    geometry.setIndex(indices);
    geometry.computeVertexNormals();
    return geometry;
    }

    // Load roads GeoJSON once and build ribbon meshes in plane local space
    function loadRoads() {
    if (roadsLoaded) return Promise.resolve();
    if (roadsLoadPromise) return roadsLoadPromise;
    roadsLoadPromise = (async () => {
        try {
        const response = await fetch(ROADS_GEOJSON_URL);
        if (!response.ok) {
        console.error("Failed to fetch roads:", response.status, response.statusText);
        return;
        }
        const geojson = await response.json();

        if (!geojson.features || !Array.isArray(geojson.features)) {
        console.error("Invalid GeoJSON structure");
        return;
        }

        const crs = detectRoadsGeoCrs(geojson);
        console.log("Roads GeoJSON CRS mode:", crs);

        let roadCount = 0;
        const roadGeometries = [];

        for (const feature of geojson.features) {
        const lineStrings = geometryToRoadLineStrings(feature.geometry);
        if (lineStrings.length === 0) continue;

        for (const lineString of lineStrings) {
            if (!Array.isArray(lineString) || lineString.length < 2) continue;

            const projectedPoints = [];

            for (const coord of lineString) {
            const [x, z] = roadCoordToPlaneXZ(coord, crs);
            if (isNaN(x) || isNaN(z)) continue;

            projectedPoints.push(new THREE.Vector3(x, z, 0.005));
            }

            if (projectedPoints.length < 2) continue;

            const segGeom = createRibbonGeometry(projectedPoints, ROAD_RIBBON_WIDTH, 0, false);
            if (segGeom) {
            roadGeometries.push(segGeom);
            roadCount++;
            }
        }
        }

        if (roadGeometries.length > 0) {
        const merged = mergeGeometries(roadGeometries);
        for (const g of roadGeometries) g.dispose();
        if (merged) {
            merged.computeVertexNormals();
            merged.computeBoundingSphere();
            roadMergedGeometry = merged;
        }
        }

        roadsLoaded = true;
        console.log(`Loaded ${roadCount} road segments → merged mesh`);
        } catch (err) {
        console.error("Failed to load roads:", err);
        } finally {
        roadsLoadPromise = null;
        }
    })();
    return roadsLoadPromise;
    }

    // Single merged road mesh (one draw call) — geometry built in loadRoads
    function addRoadsToPlane() {
    if (!placedPlane || !roadMergedGeometry) return;

    if (!placedPlane.userData.roadsGroup) {
        const roadsGroup = new THREE.Group();
        roadsGroup.name = "roadsGroup";
        roadsGroup.rotation.y = 0;
        placedPlane.add(roadsGroup);

        const roadMaterial = new THREE.MeshBasicMaterial({
        color: 0x000000,
        side: THREE.DoubleSide,
        polygonOffset: true,
        polygonOffsetFactor: -1,
        polygonOffsetUnits: -1
        });
        const roadMesh = new THREE.Mesh(roadMergedGeometry, roadMaterial);
        roadMesh.userData = { isRoad: true, mergedRoads: true };
        roadMesh.renderOrder = -2;
        roadsGroup.add(roadMesh);

        placedPlane.userData.roadsGroup = roadsGroup;
    }
    applyRoadsVisibility();
    }

    function removeRoadsFromPlane() {
    const roadsGroup = placedPlane?.userData?.roadsGroup;
    if (roadsGroup) {
        roadsGroup.traverse((o) => {
            if (o.geometry) o.geometry.dispose();
            if (o.material) o.material.dispose();
        });
        while (roadsGroup.children.length > 0) roadsGroup.remove(roadsGroup.children[0]);
    }
    }

    // Placement mode toggle
    placementToggleButton.addEventListener("click", () => {
    blockNextSelect = true;
    setPlacementMode(!placementMode);
    });

    enterARButton.addEventListener("click", () => {
    startAR().catch((err) => {
        console.error(err);
        alert("Failed to start AR: " + err.message);
    });
    });

    function updatePointsLabel() {
    const labelEl = document.getElementById("event-date-label");
    if (!labelEl) return;
    const count = pointsOptions[pointsToShowIndex] ?? pointsOptions[pointsOptions.length - 1];
    const rawTotal = getRawShorterTripEventCount();
    labelEl.textContent = rawTotal ? `${count} / ${rawTotal} pts` : "—";
    }

    function populatePointsFilter() {
    updatePointsLabel();
    syncBrowsePanelVisibility();
    }

    function populateTripFilter() {
    updateTripLabels();
    updateCompareDurationButton();
    syncBrowsePanelVisibility();
    }

    function updateTripLabels() {
    const label031 = document.getElementById("trip-031-label");
    const label0401 = document.getElementById("trip-0401-label");
    const n031 = trips3.length;
    const n0401 = trips4.length;
    if (label031) {
        const idx = Math.min(currentTripIndex031, Math.max(0, n031 - 1));
        const t = trips3[idx];
        label031.textContent = n031 ? `${idx + 1}/${n031} (${t?.tripId ?? "—"})` : "—";
    }
    if (label0401) {
        const idx = Math.min(currentTripIndex0401, Math.max(0, n0401 - 1));
        const t = trips4[idx];
        label0401.textContent = n0401 ? `${idx + 1}/${n0401} (${t?.tripId ?? "—"})` : "—";
    }
    }

    const eventDatePrev = document.getElementById("event-date-prev");
    const eventDateNext = document.getElementById("event-date-next");
    const eventDateLabel = document.getElementById("event-date-label");

    const dateUiElements = [eventDatePrev, eventDateNext, eventDateLabel].filter(Boolean);
    dateUiElements.forEach((el) => {
    ["pointerdown", "mousedown", "touchstart", "click"].forEach((evt) => {
        el.addEventListener(evt, () => { blockNextSelect = true; });
    });
    });

    // Prev/next points count (rebuild markers with more/fewer points)
    function changePointsCount(direction) {
    pointsToShowIndex = (pointsToShowIndex + direction + pointsOptions.length) % pointsOptions.length;
    updatePointsLabel();
    rebuildEventMarkersForActiveDate();
    }

    if (eventDatePrev) {
    eventDatePrev.addEventListener("click", () => {
        blockNextSelect = true;
        changePointsCount(-1);
    });
    }

    if (eventDateNext) {
    eventDateNext.addEventListener("click", () => {
        blockNextSelect = true;
        changePointsCount(1);
    });
    }

    function changeTrip031(direction) {
    const max = trips3.length;
    if (max === 0) return;
    currentTripIndex031 = (currentTripIndex031 + direction + max) % max;
    updateTripLabels();
    refreshPointsOptions(false);
    rebuildEventMarkersForActiveDate();
    }
    function changeTrip0401(direction) {
    const max = trips4.length;
    if (max === 0) return;
    currentTripIndex0401 = (currentTripIndex0401 + direction + max) % max;
    updateTripLabels();
    refreshPointsOptions(false);
    rebuildEventMarkersForActiveDate();
    }
    const trip031Prev = document.getElementById("trip-031-prev");
    const trip031Next = document.getElementById("trip-031-next");
    const trip0401Prev = document.getElementById("trip-0401-prev");
    const trip0401Next = document.getElementById("trip-0401-next");
    [trip031Prev, trip031Next, trip0401Prev, trip0401Next].forEach((el) => {
    if (!el) return;
    ["pointerdown", "mousedown", "touchstart"].forEach((evt) => el.addEventListener(evt, () => { blockNextSelect = true; }));
    });
    if (trip031Prev) trip031Prev.addEventListener("click", () => { blockNextSelect = true; changeTrip031(-1); });
    if (trip031Next) trip031Next.addEventListener("click", () => { blockNextSelect = true; changeTrip031(1); });
    if (trip0401Prev) trip0401Prev.addEventListener("click", () => { blockNextSelect = true; changeTrip0401(-1); });
    if (trip0401Next) trip0401Next.addEventListener("click", () => { blockNextSelect = true; changeTrip0401(1); });

    function updateCompareDurationButton() {
    const btn = document.getElementById("compare-duration-btn");
    if (btn) btn.textContent = compareTripDuration ? "Compare duration: ON" : "Compare duration: OFF";
    }
    const compareDurationBtn = document.getElementById("compare-duration-btn");
    if (compareDurationBtn) {
    compareDurationBtn.addEventListener("click", () => {
        blockNextSelect = true;
        compareTripDuration = !compareTripDuration;
        updateCompareDurationButton();
        rebuildEventMarkersForActiveDate();
    });
    ["pointerdown", "mousedown", "touchstart"].forEach((evt) => {
        compareDurationBtn.addEventListener(evt, () => { blockNextSelect = true; });
    });
    }

    function wireVisibilityToggle(btn, onToggle) {
    if (!btn) return;
    btn.addEventListener("click", () => {
        blockNextSelect = true;
        onToggle();
    });
    ["pointerdown", "mousedown", "touchstart"].forEach((evt) => {
        btn.addEventListener(evt, () => { blockNextSelect = true; });
    });
    }

    wireVisibilityToggle(toggleMapSurfaceBtn, () => {
    showMapSurface = !showMapSurface;
    toggleMapSurfaceBtn.classList.toggle("off", !showMapSurface);
    applyMapSurfaceVisibility();
    });

    wireVisibilityToggle(toggleRoadsBtn, () => {
    showRoads = !showRoads;
    toggleRoadsBtn.classList.toggle("off", !showRoads);
    applyRoadsVisibility();
    });

    wireVisibilityToggle(toggleGuideTimelinesBtn, () => {
    showGuideTimelines = !showGuideTimelines;
    toggleGuideTimelinesBtn.classList.toggle("off", !showGuideTimelines);
    applyGuideTimelinesVisibility();
    });

    if (tapCaptureEl) {
        const onTapCapture = () => {
        if (blockNextSelect) return;
        if (xrSession && !placementMode) runTapToInspect();
        };
        tapCaptureEl.addEventListener("touchend", onTapCapture, { passive: true });
        tapCaptureEl.addEventListener("click", onTapCapture);
    }
})();
