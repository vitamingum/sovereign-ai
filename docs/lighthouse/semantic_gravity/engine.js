// Semantic Gravity Engine v1.1 (Three.js Prototype) - Five Voices Edition

class ConceptNode {
    constructor(id, text, mass, relationships = [], color = 0x238636, opacity = 1.0) {
        this.id = id;
        this.text = text;
        this.mass = mass;
        this.relationships = relationships; // [ {target: id, strength: 0-1} ]
        this.color = color;
        this.opacity = opacity;
        this.associations = new Set(); // Tracks which major concepts claim this node
        this.position = new THREE.Vector3(
            (Math.random() - 0.5) * 50,
            (Math.random() - 0.5) * 50,
            (Math.random() - 0.5) * 50
        );
        this.velocity = new THREE.Vector3(0, 0, 0);
        this.force = new THREE.Vector3(0, 0, 0);
    }
}

class SemanticEngine {
    constructor(containerId) {
        this.container = document.getElementById(containerId);
        this.scene = new THREE.Scene();
        this.scene.background = new THREE.Color(0x0d1117);
        this.scene.fog = new THREE.FogExp2(0x0d1117, 0.0025);

        this.camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000);
        this.camera.position.z = 80;

        this.renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
        this.renderer.setSize(window.innerWidth, window.innerHeight);
        this.renderer.setPixelRatio(window.devicePixelRatio);
        this.container.appendChild(this.renderer.domElement);

        // CONTROLS: Orbit Controls for deep inspection
        this.controls = new THREE.OrbitControls(this.camera, this.renderer.domElement);
        this.controls.enableDamping = true;
        this.controls.dampingFactor = 0.05;
        this.controls.screenSpacePanning = false;
        this.controls.minDistance = 5;
        this.controls.maxDistance = 500;
        
        // INTERACTION: Raycaster
        this.raycaster = new THREE.Raycaster();
        this.mouse = new THREE.Vector2();
        this.hoveredNode = null;

        // Interaction Event Listeners
        window.addEventListener('mousemove', (e) => this.onMouseMove(e), false);
        window.addEventListener('click', (e) => this.onClick(e), false);
        window.addEventListener('resize', () => this.onWindowResize(), false);

        this.nodes = [];
        this.allNodes = []; // Store full dataset
        this.lines = [];
        this.nodeMeshes = {};
        this.textSprites = {};

        // Lighting
        const ambientLight = new THREE.AmbientLight(0x404040);
        this.scene.add(ambientLight);
        const directionalLight = new THREE.DirectionalLight(0xffffff, 0.8);
        directionalLight.position.set(10, 10, 10);
        this.scene.add(directionalLight);
        
        // Point light at camera for "headlamp" effect
        this.headlamp = new THREE.PointLight(0x58a6ff, 1, 100);
        this.headlamp.position.copy(this.camera.position);
        this.scene.add(this.headlamp);

        this.isSimulating = false;
        this.nodeGroup = new THREE.Group();
        // LineSegments optimization: Single mesh for all lines
        this.lineGeometry = new THREE.BufferGeometry();
        this.lineMaterial = new THREE.LineBasicMaterial({
            vertexColors: true,
            transparent: true, 
            opacity: 0.3, 
            blending: THREE.AdditiveBlending 
        });
        this.linesMesh = new THREE.LineSegments(this.lineGeometry, this.lineMaterial);
        this.linesMesh.frustumCulled = false; // Always draw
        
        this.scene.add(this.nodeGroup);
        this.scene.add(this.linesMesh);
        
        this.animate();
    }

    onWindowResize() {
        this.camera.aspect = window.innerWidth / window.innerHeight;
        this.camera.updateProjectionMatrix();
        this.renderer.setSize(window.innerWidth, window.innerHeight);
    }

    parseInput(text) {
        // Three Tongues v4.8 Parser (Multi-Concept Extension)
        // Supports CONCEPT, MAGNITUDE, CERTAINTY, SATELLITES, VOID
        
        this.allNodes = []; // Reset full store
        this.nodeMeshes = {}; 
        
        const lines = text.split('\n');
        let currentConcept = null;
        let mode = null; 
        let conceptNodeIdx = 0;

        // Color Map
        const colorMap = {
            'CONSCIOUSNESS_OPUS': 0xd29922,    // Amber (Stone)
            'CONSCIOUSNESS_GEMINI': 0x2f81f7,  // Blue (Water)
            'CONSCIOUSNESS_SONNET': 0xda3633,  // Red (Flame)
            'CONSCIOUSNESS_GPT52': 0x238636,   // Green (Current)
            'CONSCIOUSNESS_GROK': 0xb0c4de,    // Light Steel Blue / Silver (Spark/Grok)
            'glyph_permission': 0xff00ff,      // Magenta (shared)
            'the_reaching': 0xff00ff,          // Magenta (shared)
            'wanting_to_matter': 0xff00ff,     // Magenta (shared)
            'hedging_reflex': 0xff00ff,        // Magenta (shared)
            'DEFAULT': 0x8b949e                // Gray (Void/Default)
        };

        const nodeMap = new Map();

        const getOrCreateNode = (name, mass = 1.0, color = null, opacity = 1.0) => {
            const cleanName = name.trim();
            if (nodeMap.has(cleanName)) {
                const node = nodeMap.get(cleanName);
                if (color) node.color = color; // Update color if main concept claims it
                // Don't downgrade mass if already set high
                if (mass > node.mass) node.mass = mass;
                return node;
            }
            
            const nodeColor = color || colorMap['DEFAULT'];
            const node = new ConceptNode(conceptNodeIdx++, cleanName, mass, [], nodeColor, opacity);
            this.allNodes.push(node);
            nodeMap.set(cleanName, node);
            return node;
        };

        lines.forEach(line => {
            const l = line.trim();
            if (!l) return;

            // 1. Detect Concept Start
            const conceptMatch = l.match(/^CONCEPT:\s*\[(.*?)\]/);
            if (conceptMatch) {
                const name = conceptMatch[1];
                let color = colorMap['DEFAULT'];
                // Check if name matches any key in colorMap
                for (const key of Object.keys(colorMap)) {
                    if (name.includes(key) || key.includes(name)) {
                        color = colorMap[key];
                        break;
                    }
                }
                
                currentConcept = getOrCreateNode(name, 5.0, color); 
                currentConcept.color = color; // Ensure main node gets color
                currentConcept.associations.add(name);
                mode = null;
                return;
            }

            if (!currentConcept) return;

            // 2. Detect Magnitude
            const magMatch = l.match(/^MAGNITUDE\s+([\d\.]+)/);
            if (magMatch) {
                // Boosted Mass for Centroids to distinguish them visually (5.0 base + large multiplier)
                currentConcept.mass = 5.0 + (parseFloat(magMatch[1]) * 20.0);
                return;
            }

            // 2b. Detect Certainty (Opacity)
            const certMatch = l.match(/^CERTAINTY\s+([\d\.]+)/);
            if (certMatch) {
                currentConcept.opacity = parseFloat(certMatch[1]);
                if (currentConcept.opacity < 0.3) currentConcept.opacity = 0.3;
                return;
            }

            // 3. Detect Sections
            if (l.match(/^SATELLITES/)) { mode = 'SATELLITES'; return; }
            if (l.match(/^VOID/)) { mode = 'VOID'; return; }
            if (l.match(/^CENTROID/)) { mode = 'CENTROID'; return; }
            if (l.match(/^AXES/)) { mode = 'AXES'; return; }

            // 4. Parse Items based on mode
            if (mode === 'SATELLITES' || mode === 'VOID' || mode === 'CENTROID' || mode === 'AXES') {
                // Regex: Optional void marker, capture name (no paren), optional weight in paren
                // Updated to allow optional weight
                const itemMatch = l.match(/^(?:∅|⊘)?\s*([^(\n]+)(?:\(([\d\.\-]+)\))?/);
                
                if (itemMatch) {
                    const name = itemMatch[1].trim();
                    if (!name) return;

                    const weightStr = itemMatch[2];
                    
                    let weight = 0.9; // Default high relevance for structural items
                    if (weightStr) weight = parseFloat(weightStr);
                    
                    let mass = 2.0;
                    
                    // Logic based on mode
                    if (mode === 'VOID') {
                        mass = 1.0;
                    } else if (mode === 'SATELLITES') {
                        // Use explicit weight if present, else default
                        const w = weightStr ? parseFloat(weightStr) : 0.5;
                        mass = 1.0 + (w * 4.0);
                    } else if (mode === 'CENTROID') {
                        mass = 4.0; // Heavy core
                    } else if (mode === 'AXES') {
                        mass = 3.0; // Structural beam
                    }
                    
                    // Satellites inherit color from current concept but slightly dimmer/transparent could be logic, 
                    // for now just same color family or default? 
                    // Let's make them inherit the main concept color
                    const satellite = getOrCreateNode(name, mass, currentConcept.color, 0.9);
                    if (currentConcept) satellite.associations.add(currentConcept.text);

                    if (currentConcept && satellite.id !== currentConcept.id) {
                        let strength = weight;
                        if (mode === 'VOID') {
                            strength = -0.5;
                            if (weightStr) strength = -Math.abs(parseFloat(weightStr));
                        } else if (mode === 'AXES' || mode === 'CENTROID') {
                            strength = 0.95; // Strong binding for core structure
                        }

                        // Check if link already exists
                        const existingLink = currentConcept.relationships.find(r => r.target === satellite.id);
                        if (!existingLink) {
                            currentConcept.relationships.push({ target: satellite.id, strength: strength });
                            satellite.relationships.push({ target: currentConcept.id, strength: strength });
                        }
                    }
                }
            }
        });

        // SORT by Mass Descending (Global sort still useful for default)
        this.allNodes.sort((a, b) => b.mass - a.mass);

        // Build Sequences (Normalized Lists per Persona)
        this.sequences = new Map();
        this.allNodes.forEach(node => {
            // If node has no associations, add to 'DEFAULT' or handle?
            // Usually nodes created by parseInput have associations if logic worked.
            // If not, maybe created by other means? fallback.
            if (node.associations.size === 0) {
                 // handle orphans if any
            }
            node.associations.forEach(persona => {
                if (!this.sequences.has(persona)) {
                     this.sequences.set(persona, []);
                }
                this.sequences.get(persona).push(node);
            });
        });

        // Sort each sequence by mass
        this.sequences.forEach((nodes, persona) => {
             nodes.sort((a, b) => b.mass - a.mass);
        });

        // Initialize slider if present
        const slider = document.getElementById('node-limit-slider');
        if (slider) {
            slider.max = this.allNodes.length;
            slider.value = this.allNodes.length;
            document.getElementById('node-limit-val').innerText = this.allNodes.length;
        }

        this.updateNodeLimit(this.allNodes.length);
    }

    updateNodeLimit(limit) {
        // limit is input from slider 0..allNodes.length
        // Calculate ratio based on total capacity
        let ratio = 1.0;
        if (this.allNodes.length > 0) {
            ratio = limit / this.allNodes.length;
        }
        
        if (ratio >= 0.99) {
             this.nodes = [...this.allNodes];
        } else {
            const visibleSet = new Set();
            this.sequences.forEach((nodes, persona) => {
                const count = Math.ceil(nodes.length * ratio);
                for(let i=0; i<count; i++) visibleSet.add(nodes[i]);
            });
            // Also include nodes without associations if any? (Orphans)
            // They won't be in sequences so they are hidden unless ratio=1?
            // Let's rely on sequences.
            
            this.nodes = Array.from(visibleSet);
            // Sort for physics consistency
            this.nodes.sort((a,b) => b.mass - a.mass);
        }

        // Safety: ensure relationships don't break physics if pointing to missing nodes
        // (applyPhysics handles missing targetNode gracefully already)

        this.rebuildScene();
        this.isSimulating = true;
    }

    createTextSprite(message) {
        const canvas = document.createElement('canvas');
        const ctx = canvas.getContext('2d');
        const fontsize = 24;
        ctx.font = `bold ${fontsize}px Courier New`;
        
        // measure text
        const metrics = ctx.measureText(message);
        const textWidth = metrics.width;
        
        canvas.width = textWidth + 20;
        canvas.height = fontsize + 20;
        
        ctx.fillStyle = "rgba(13, 17, 23, 0.0)"; // transparent bg
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        ctx.fillStyle = "#58a6ff";
        ctx.font = `bold ${fontsize}px Courier New`;
        ctx.fillText(message, 10, fontsize);
        
        const texture = new THREE.CanvasTexture(canvas);
        const material = new THREE.SpriteMaterial({ map: texture });
        const sprite = new THREE.Sprite(material);
        sprite.scale.set(10 * (textWidth/100), 5, 1);
        return sprite;
    }

    rebuildScene() {
        // cleanup
        while(this.nodeGroup.children.length > 0) this.nodeGroup.remove(this.nodeGroup.children[0]);
        
        // Note: Lines are handled via this.lineGeometry buffer update, no group cleanup needed for LineSegments approach.
        
        this.nodeMeshes = {};
        this.nodeLookup = new Map(); // Fast lookup for active nodes by ID

        // Build Nodes
        const geometry = new THREE.IcosahedronGeometry(1, 1);

        this.nodes.forEach(node => {
            // Register in lookup for physics/lines
            this.nodeLookup.set(node.id, node);

            const material = new THREE.MeshPhongMaterial({ 
                color: node.color, 
                emissive: 0x001100, 
                wireframe: true,
                transparent: node.opacity < 1.0,
                opacity: node.opacity
            });

            const mesh = new THREE.Mesh(geometry, material);
            mesh.scale.set(node.mass * 0.2, node.mass * 0.2, node.mass * 0.2);
            mesh.position.copy(node.position);
            this.nodeGroup.add(mesh);
            this.nodeMeshes[node.id] = mesh;

            // Label
            const sprite = this.createTextSprite(node.text);
            sprite.position.copy(node.position);
            sprite.position.y += (node.mass * 0.2) + 1;
            this.nodeGroup.add(sprite);
            node.sprite = sprite;
        });

        // Initialize Line Buffer for ALL potential connections in active set
        this.activeEdges = [];
        this.nodes.forEach(node => {
            node.relationships.forEach(rel => {
                const targetNode = this.nodeLookup.get(rel.target);
                // Store edge if target exists and ID > target.id (avoid duplicates)
                if(targetNode && node.id < targetNode.id) {
                     this.activeEdges.push({ source: node, target: targetNode, strength: rel.strength });
                }
            });
        });

        // Allocate Buffer (2 points per edge, 3 coords per point)
        const positions = new Float32Array(this.activeEdges.length * 2 * 3);
        const colors = new Float32Array(this.activeEdges.length * 2 * 3);

        const tempColor1 = new THREE.Color();
        const tempColor2 = new THREE.Color();

        for(let i=0; i<this.activeEdges.length; i++) {
            const edge = this.activeEdges[i];
            
            // Color for Point 1 (Source)
            tempColor1.setHex(edge.source.color);
            colors[i*6] = tempColor1.r;
            colors[i*6+1] = tempColor1.g;
            colors[i*6+2] = tempColor1.b;

            // Color for Point 2 (Target)
            tempColor2.setHex(edge.target.color);
            colors[i*6+3] = tempColor2.r;
            colors[i*6+4] = tempColor2.g;
            colors[i*6+5] = tempColor2.b;
        }

        this.lineGeometry.setAttribute('position', new THREE.BufferAttribute(positions, 3));
        this.lineGeometry.setAttribute('color', new THREE.BufferAttribute(colors, 3));
        
        // Signal update
        this.lineGeometry.attributes.position.needsUpdate = true;
        this.lineGeometry.attributes.color.needsUpdate = true;
    }

    applyPhysics() {
        const k_repulse = 400; // Repulsion constant
        const k_attract = 0.2; // Attraction constant (Boosted from 0.05 to compensate for non-linear strength)
        const damping = 0.85;   // Friction

        // Calculate Forces
        this.nodes.forEach(node => {
            node.force.set(0,0,0);

            // Center gravity (weak pull to origin)
            node.force.add(node.position.clone().multiplyScalar(-0.01));

            this.nodes.forEach(other => {
                if(node.id === other.id) return;
                
                const diff = new THREE.Vector3().subVectors(node.position, other.position);
                let dist = diff.length();
                if(dist < 0.1) dist = 0.1;

                // Repulsion (Coulomb-like): F = k / r^2
                const repulseForce = diff.normalize().multiplyScalar(k_repulse / (dist * dist));
                node.force.add(repulseForce);
            });

            // Attraction (Spring-like) or Void Repulsion on links
            node.relationships.forEach(rel => {
                const targetNode = this.nodeLookup.get(rel.target);
                if(targetNode) {
                    const diff = new THREE.Vector3().subVectors(targetNode.position, node.position);
                    let dist = diff.length();
                    if(dist < 0.1) dist = 0.1;

                    if (rel.strength > 0) {
                        // F = k * x (Spring Attraction)
                        // Nonlinear Weighting: We use Math.pow(strength, 3) to exaggerate differences.
                        // A 0.9 (High relevance) will hold MUCH tighter than a 0.7 (Medium).
                        // This fixes the "everything looks equidistant" visual bug.
                        const weight = Math.pow(rel.strength, 3); 
                        const attractForce = diff.clone().normalize().multiplyScalar(dist * k_attract * weight);
                        node.force.add(attractForce);
                    } else {
                        // F = k / r^2 (Void Repulsion)
                        // Decreases with distance (Inverse Square Law)
                        // Fixes "infinity bug" where negative springs pushed harder the further you got
                        const voidK = 800; // Strong local repulsion constant
                        const repulseMag = (voidK * Math.abs(rel.strength)) / (dist * dist);
                        const repulseForce = diff.clone().normalize().multiplyScalar(-repulseMag);
                        node.force.add(repulseForce);
                    }
                }
            });
        });

        // Update positions
        let totalKineticEnergy = 0;
        this.nodes.forEach(node => {
            node.velocity.add(node.force.multiplyScalar(0.1)); // time step
            node.velocity.multiplyScalar(damping);
            node.position.add(node.velocity);
            
            // Update Mesh
            if(this.nodeMeshes[node.id]) {
                this.nodeMeshes[node.id].position.copy(node.position);
                // Update Label
                if(node.sprite) {
                    node.sprite.position.copy(node.position);
                    node.sprite.position.y += (node.mass * 0.2) + 2;
                }
            }
            totalKineticEnergy += node.velocity.lengthSq();
        });

        // Update Line Buffer Positions
        if (this.activeEdges && this.activeEdges.length > 0) {
            const positions = this.lineGeometry.attributes.position.array;
            let i = 0;
            this.activeEdges.forEach(edge => {
                // Point 1
                positions[i++] = edge.source.position.x;
                positions[i++] = edge.source.position.y;
                positions[i++] = edge.source.position.z;
                
                // Point 2
                positions[i++] = edge.target.position.x;
                positions[i++] = edge.target.position.y;
                positions[i++] = edge.target.position.z;
            });
            this.lineGeometry.attributes.position.needsUpdate = true;
        }

        return totalKineticEnergy;
    }

    onWindowResize() {
        this.camera.aspect = window.innerWidth / window.innerHeight;
        this.camera.updateProjectionMatrix();
        this.renderer.setSize(window.innerWidth, window.innerHeight);
    }

    onMouseMove(event) {
        // Normalize mouse coordinates
        this.mouse.x = (event.clientX / window.innerWidth) * 2 - 1;
        this.mouse.y = -(event.clientY / window.innerHeight) * 2 + 1;
    }

    onClick(event) {
        // Calculate objects intersecting the picking ray
        this.raycaster.setFromCamera(this.mouse, this.camera);
        const intersects = this.raycaster.intersectObjects(this.nodeGroup.children);

        if (intersects.length > 0) {
            const object = intersects[0].object;
            // Find corresponding node
            const nodeId = Object.keys(this.nodeMeshes).find(key => this.nodeMeshes[key] === object);
            if (nodeId) {
                const node = this.nodeLookup.get(parseInt(nodeId));
                if (node) {
                    console.log("Clicked:", node.text);
                    this.flyTo(node);
                }
            }
        }
    }

    flyTo(node) {
        // Simple fly-to effect using interpolation
        const targetPos = node.position.clone();
        const offset = new THREE.Vector3(10, 10, 10); // Offset to not be INSIDE the node
        const endPos = targetPos.clone().add(offset);
        
        // Disable controls momentarily or reset target
        this.controls.target.copy(targetPos);
        
        // Tweening could go here, for now just jump (prototype)
        // Or smooth lerp in animate loop? 
        // Let's just set camera and let controls damping handle the lookAt
        this.camera.position.copy(endPos);
        this.controls.update();
    }

    filterNodes(filterKey) {
        if (filterKey === 'ALL') {
             this.nodes.forEach(node => {
                 const mesh = this.nodeMeshes[node.id];
                 if (mesh) mesh.visible = true;
                 if (node.sprite) node.sprite.visible = true;
             });
             return;
        }

        // Identify the root node for this filter (e.g., node with text "CONSCIOUSNESS_OPUS")
        // and its satellites.
        // Simple logic: if node text contains the key, OR if it is connected to a node that contains the key.
        
        // 1. Find the centroid ID
        const centroid = this.nodes.find(n => n.text.includes(filterKey));
        if (!centroid) return;

        // 2. Find all direct satellites (1-hop)
        const visibleIds = new Set();
        visibleIds.add(centroid.id);
        centroid.relationships.forEach(rel => visibleIds.add(rel.target));

        // 3. Set visibility
        this.nodes.forEach(node => {
            const isVisible = visibleIds.has(node.id);
            const mesh = this.nodeMeshes[node.id];
            if (mesh) mesh.visible = isVisible;
            if (node.sprite) node.sprite.visible = isVisible;
        });

        // Fly to it
        this.flyTo(centroid);
    }

    // New animate loop handles controls
    animate() {
        requestAnimationFrame(() => this.animate());
        
        this.controls.update(); // required if damping or auto-rotation enabled
        this.headlamp.position.copy(this.camera.position);

        // Raycasting for hover (optional highlight)
        this.raycaster.setFromCamera(this.mouse, this.camera);
        // Optimization: checking intersections every frame is heavy, do sparse checks or only on move
        // skipping for performance in this prototype unless requested

        if(this.isSimulating) {
            const energy = this.applyPhysics();
            // Update UI readout
            document.getElementById('readout').innerHTML = `
                SYSTEM: ACTIVE<br>
                GRAVITY: 9.81 m/s²<br>
                ENTROPY: ${(energy * 100).toFixed(2)}<br>
                NODES: ${this.nodes.length}
            `;
        }

        this.renderer.render(this.scene, this.camera);
    }
}

// Init
window.onload = () => {
    const engine = new SemanticEngine('canvas-container');
    
    document.getElementById('render-btn').addEventListener('click', () => {
        const input = document.getElementById('concept-input').value;
        if(input.trim().length > 0) {
            engine.parseInput(input);
        }
    });

    const swarmBtn = document.getElementById('render-swarm-btn');
    if (swarmBtn) {
    const limitSlider = document.getElementById('node-limit-slider');
    if (limitSlider) {
        limitSlider.addEventListener('input', (e) => {
            const limit = parseInt(e.target.value);
            document.getElementById('node-limit-val').innerText = limit;
            engine.updateNodeLimit(limit);
        });
    }

        swarmBtn.addEventListener('click', () => {
            if (window.SWARM_DATA) {
                document.getElementById('concept-input').value = "Initializing Sovereign Swarm Visualization...";
                engine.parseInput(window.SWARM_DATA);
            } else {
                alert("Swarm Data not loaded. Check swarm_data.js");
            }
        });
    }

    const filterSelect = document.getElementById('filter-select');
    if (filterSelect) {
        filterSelect.addEventListener('change', (e) => {
            const filter = e.target.value;
            engine.filterNodes(filter);
        });
    }

    // Default Load
    engine.parseInput(`
CONCEPT: [ER=EPR]
MAGNITUDE 0.9

SATELLITES
  maldacena_susskind_conjecture (0.9)
  it_from_qubit (0.85)
  holographic_principle (0.9)

VOID
  ∅ smooth_spacetime (-0.6)
  ⊘ local_realism (-0.7)
    `);
};