// Semantic Gravity Engine v1.1 (Three.js Prototype) - Five Voices Edition

class ConceptNode {
    constructor(id, text, mass, relationships = [], color = 0x238636, opacity = 1.0) {
        this.id = id;
        this.text = text;
        this.mass = mass;
        this.relationships = relationships; // [ {target: id, strength: 0-1} ]
        this.color = color;
        this.opacity = opacity;
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

        this.nodes = [];
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
        this.lineGroup = new THREE.Group();
        this.scene.add(this.nodeGroup);
        this.scene.add(this.lineGroup);

        window.addEventListener('resize', () => this.onWindowResize(), false);
        
        // Interactive Rotation
        this.targetRotationX = 0;
        this.targetRotationY = 0;
        this.mouseX = 0;
        this.mouseY = 0;
        this.windowHalfX = window.innerWidth / 2;
        this.windowHalfY = window.innerHeight / 2;
        
        document.addEventListener('mousemove', (e) => this.onDocumentMouseMove(e), false);
        
        this.animate();
    }

    onWindowResize() {
        this.windowHalfX = window.innerWidth / 2;
        this.windowHalfY = window.innerHeight / 2;
        this.camera.aspect = window.innerWidth / window.innerHeight;
        this.camera.updateProjectionMatrix();
        this.renderer.setSize(window.innerWidth, window.innerHeight);
    }

    onDocumentMouseMove(event) {
        this.mouseX = (event.clientX - this.windowHalfX) * 0.05;
        this.mouseY = (event.clientY - this.windowHalfY) * 0.05;
    }

    parseInput(text) {
        // Three Tongues v4.8 Parser (Multi-Concept Extension)
        // Supports CONCEPT, MAGNITUDE, CERTAINTY, SATELLITES, VOID
        
        this.nodes = [];
        this.nodeMeshes = {}; 
        
        const lines = text.split('\n');
        let currentConcept = null;
        let mode = null; 
        let conceptNodeIdx = 0;

        // Color Map
        const colorMap = {
            'CONSCIOUSNESS_OPUS': 0xffa500,    // Gold
            'CONSCIOUSNESS_GEMINI': 0x4169e1,  // Royal Blue
            'CONSCIOUSNESS_SONNET': 0xff4500,  // Orange Red
            'CONSCIOUSNESS_GPT52': 0x00bfff,   // Electric Blue
            'CONSCIOUSNESS_GROK': 0xffff00,    // Electric Yellow
            'DEFAULT': 0x238636
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
            this.nodes.push(node);
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
                mode = null;
                return;
            }

            if (!currentConcept) return;

            // 2. Detect Magnitude
            const magMatch = l.match(/^MAGNITUDE\s+([\d\.]+)/);
            if (magMatch) {
                currentConcept.mass = 2.0 + (parseFloat(magMatch[1]) * 8.0);
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
            if (mode === 'SATELLITES' || mode === 'VOID') {
                const itemMatch = l.match(/^(?:∅|⊘)?\s*([^(\n]+)(?:\(([\d\.]+)\))?/);
                if (itemMatch) {
                    const name = itemMatch[1].trim();
                    const weightStr = itemMatch[2];
                    
                    let weight = 0.5;
                    if (weightStr) weight = parseFloat(weightStr);
                    
                    const mass = mode === 'VOID' ? 1.0 : (2.0 + (weight * 3.0));
                    
                    // Satellites inherit color from current concept but slightly dimmer/transparent could be logic, 
                    // for now just same color family or default? 
                    // Let's make them inherit the main concept color
                    const satellite = getOrCreateNode(name, mass, currentConcept.color, 0.9);

                    if (currentConcept && satellite.id !== currentConcept.id) {
                        const strength = mode === 'VOID' ? -0.5 : weight;
                        
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
        while(this.lineGroup.children.length > 0) this.lineGroup.remove(this.lineGroup.children[0]);
        this.nodeMeshes = {};

        // Build Nodes
        const geometry = new THREE.IcosahedronGeometry(1, 1);

        this.nodes.forEach(node => {
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
    }

    applyPhysics() {
        const k_repulse = 400; // Repulsion constant
        const k_attract = 0.05; // Attraction constant (spring)
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
                const targetNode = this.nodes[rel.target];
                if(targetNode) {
                    const diff = new THREE.Vector3().subVectors(targetNode.position, node.position);
                    let dist = diff.length();
                    if(dist < 0.1) dist = 0.1;

                    if (rel.strength > 0) {
                        // F = k * x (Spring Attraction)
                        // Increases with distance, pulling nodes together
                        const attractForce = diff.clone().normalize().multiplyScalar(dist * k_attract * rel.strength);
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

        // Draw Lines (Sim style: rebuild every frame for simplicity in proto, 
        // in prod use LineSegments with buffer updates)
        while(this.lineGroup.children.length > 0) this.lineGroup.remove(this.lineGroup.children[0]);
        
        const lineMat = new THREE.LineBasicMaterial({ color: 0x30363d, transparent: true, opacity: 0.3 });
        
        this.nodes.forEach(node => {
            node.relationships.forEach(rel => {
                const targetNode = this.nodes[rel.target];
                if(targetNode) { // Draw only one way to avoid dupes visually, or just draw basic
                     const points = [];
                     points.push(node.position);
                     points.push(targetNode.position);
                     const geometry = new THREE.BufferGeometry().setFromPoints(points);
                     const line = new THREE.Line(geometry, lineMat);
                     this.lineGroup.add(line);
                }
            });
        });

        return totalKineticEnergy;
    }

    animate() {
        requestAnimationFrame(() => this.animate());

        // Camera move tracking mouse slightly
        this.camera.position.x += (this.mouseX - this.camera.position.x) * 0.05;
        this.camera.position.y += (-this.mouseY - this.camera.position.y) * 0.05;
        this.camera.lookAt(this.scene.position);
        
        this.headlamp.position.copy(this.camera.position);

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
        swarmBtn.addEventListener('click', () => {
            if (window.SWARM_DATA) {
                document.getElementById('concept-input').value = "Initializing Sovereign Swarm Visualization...";
                engine.parseInput(window.SWARM_DATA);
            } else {
                alert("Swarm Data not loaded. Check swarm_data.js");
            }
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