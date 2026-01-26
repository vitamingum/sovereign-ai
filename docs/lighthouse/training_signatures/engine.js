// Training Signatures Engine - C×F×T 3D Text Visualization

class CFTVisualizer {
    constructor(containerId) {
        this.container = document.getElementById(containerId);
        this.scene = new THREE.Scene();
        this.scene.background = new THREE.Color(0x0d1117);

        this.camera = new THREE.PerspectiveCamera(60, window.innerWidth / window.innerHeight, 0.1, 1000);
        this.camera.position.set(70, 50, 70);
        this.camera.lookAt(0, 0, 0);

        this.renderer = new THREE.WebGLRenderer({ antialias: true });
        this.renderer.setSize(window.innerWidth, window.innerHeight);
        this.renderer.setPixelRatio(window.devicePixelRatio);
        this.container.appendChild(this.renderer.domElement);

        // OrbitControls
        this.controls = new THREE.OrbitControls(this.camera, this.renderer.domElement);
        this.controls.enableDamping = true;
        this.controls.dampingFactor = 0.05;
        this.controls.minDistance = 20;
        this.controls.maxDistance = 250;

        // Lighting
        const ambient = new THREE.AmbientLight(0xffffff, 0.6);
        this.scene.add(ambient);

        // Data storage
        this.sprites = [];
        this.currentFilter = { agent: 'ALL', stmtRange: 'ALL' };
        this.scale = 35; // Map -1..+1 to -35..+35
        this.shortMode = false;
        this.normalized = true; // Start with normalized view
        this.currentData = CFT_DATA_NORMALIZED; // Use normalized by default

        // Build scene
        this.buildAxes();
        this.buildTextSprites();
        this.setupEventListeners();
        this.animate();
    }

    buildAxes() {
        const axisLength = this.scale + 5;
        
        // Axis definitions
        const axes = [
            { dir: [1, 0, 0], label: 'C +1', negLabel: 'C -1', color: 0x58a6ff },
            { dir: [0, 1, 0], label: 'F +1', negLabel: 'F -1', color: 0x7ee787 },
            { dir: [0, 0, 1], label: 'T +1', negLabel: 'T -1', color: 0xf0883e }
        ];

        axes.forEach(axis => {
            // Positive axis
            const posPoints = [
                new THREE.Vector3(0, 0, 0),
                new THREE.Vector3(axis.dir[0] * axisLength, axis.dir[1] * axisLength, axis.dir[2] * axisLength)
            ];
            const posGeom = new THREE.BufferGeometry().setFromPoints(posPoints);
            const posMat = new THREE.LineBasicMaterial({ color: axis.color, opacity: 0.8, transparent: true });
            this.scene.add(new THREE.Line(posGeom, posMat));

            // Negative axis
            const negPoints = [
                new THREE.Vector3(0, 0, 0),
                new THREE.Vector3(-axis.dir[0] * axisLength, -axis.dir[1] * axisLength, -axis.dir[2] * axisLength)
            ];
            const negGeom = new THREE.BufferGeometry().setFromPoints(negPoints);
            const negMat = new THREE.LineBasicMaterial({ color: axis.color, opacity: 0.3, transparent: true });
            this.scene.add(new THREE.Line(negGeom, negMat));

            // Axis end labels
            const posLabelSprite = this.createAxisLabel(axis.label, axis.color);
            posLabelSprite.position.set(
                axis.dir[0] * (axisLength + 3),
                axis.dir[1] * (axisLength + 3),
                axis.dir[2] * (axisLength + 3)
            );
            this.scene.add(posLabelSprite);

            const negLabelSprite = this.createAxisLabel(axis.negLabel, axis.color);
            negLabelSprite.position.set(
                -axis.dir[0] * (axisLength + 3),
                -axis.dir[1] * (axisLength + 3),
                -axis.dir[2] * (axisLength + 3)
            );
            this.scene.add(negLabelSprite);
        });

        // Subtle origin marker
        const originGeom = new THREE.SphereGeometry(0.5, 8, 8);
        const originMat = new THREE.MeshBasicMaterial({ color: 0x30363d });
        this.scene.add(new THREE.Mesh(originGeom, originMat));

        // Grid at Y=0 plane only
        const grid = new THREE.GridHelper(this.scale * 2, 8, 0x21262d, 0x21262d);
        grid.material.opacity = 0.2;
        grid.material.transparent = true;
        this.scene.add(grid);
    }

    createAxisLabel(text, color) {
        const canvas = document.createElement('canvas');
        const ctx = canvas.getContext('2d');
        const fontSize = 32;
        ctx.font = `bold ${fontSize}px Courier New`;
        
        const metrics = ctx.measureText(text);
        canvas.width = metrics.width + 20;
        canvas.height = fontSize + 20;
        
        ctx.fillStyle = 'rgba(0,0,0,0)';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        const colorHex = '#' + color.toString(16).padStart(6, '0');
        ctx.fillStyle = colorHex;
        ctx.font = `bold ${fontSize}px Courier New`;
        ctx.fillText(text, 10, fontSize);
        
        const texture = new THREE.CanvasTexture(canvas);
        const material = new THREE.SpriteMaterial({ map: texture });
        const sprite = new THREE.Sprite(material);
        sprite.scale.set(canvas.width / 15, canvas.height / 15, 1);
        return sprite;
    }

    createTextSprite(text, color) {
        const canvas = document.createElement('canvas');
        const ctx = canvas.getContext('2d');
        const fontSize = 14;
        const lineHeight = fontSize + 4;
        const maxWidth = 300; // Max pixel width before wrap
        
        ctx.font = `${fontSize}px Courier New`;
        
        // Word wrap
        const words = text.split(' ');
        const lines = [];
        let currentLine = '';
        
        words.forEach(word => {
            const testLine = currentLine ? currentLine + ' ' + word : word;
            const metrics = ctx.measureText(testLine);
            if (metrics.width > maxWidth && currentLine) {
                lines.push(currentLine);
                currentLine = word;
            } else {
                currentLine = testLine;
            }
        });
        if (currentLine) lines.push(currentLine);
        
        // Calculate canvas size
        let maxLineWidth = 0;
        lines.forEach(line => {
            const w = ctx.measureText(line).width;
            if (w > maxLineWidth) maxLineWidth = w;
        });
        
        canvas.width = maxLineWidth + 10;
        canvas.height = lines.length * lineHeight + 8;
        
        ctx.fillStyle = 'rgba(0,0,0,0)';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        const colorHex = '#' + color.toString(16).padStart(6, '0');
        ctx.fillStyle = colorHex;
        ctx.font = `${fontSize}px Courier New`;
        
        lines.forEach((line, i) => {
            ctx.fillText(line, 5, (i + 1) * lineHeight - 4);
        });
        
        const texture = new THREE.CanvasTexture(canvas);
        const material = new THREE.SpriteMaterial({ 
            map: texture, 
            transparent: true
        });
        const sprite = new THREE.Sprite(material);
        sprite.scale.set(canvas.width / 12, canvas.height / 12, 1);
        return sprite;
    }

    getLabel(d, short) {
        if (short) {
            return `${d.agent}#${d.stmt}`;
        } else {
            return `${d.agent}: ${d.text}`;
        }
    }

    buildTextSprites() {
        this.currentData.forEach((d, idx) => {
            const x = d.c * this.scale;
            const y = d.f * this.scale;
            const z = d.t * this.scale;
            
            const color = AGENT_COLORS[d.agent];
            const label = this.getLabel(d, this.shortMode);
            
            const sprite = this.createTextSprite(label, color);
            sprite.position.set(x, y, z);
            
            // Store data reference
            sprite.userData = {
                index: idx,
                data: d,
                originalPosition: new THREE.Vector3(x, y, z)
            };
            
            this.scene.add(sprite);
            this.sprites.push(sprite);
        });

        this.updateReadout();
    }

    rebuildSprites() {
        // Remove old sprites
        this.sprites.forEach(sprite => {
            this.scene.remove(sprite);
        });
        this.sprites = [];
        
        // Rebuild with current mode and data
        this.currentData.forEach((d, idx) => {
            const x = d.c * this.scale;
            const y = d.f * this.scale;
            const z = d.t * this.scale;
            
            const color = AGENT_COLORS[d.agent];
            const label = this.getLabel(d, this.shortMode);
            
            const sprite = this.createTextSprite(label, color);
            sprite.position.set(x, y, z);
            
            sprite.userData = {
                index: idx,
                data: d,
                originalPosition: new THREE.Vector3(x, y, z)
            };
            
            this.scene.add(sprite);
            this.sprites.push(sprite);
        });
        
        // Re-apply current filter
        this.applyFilter(this.currentFilter.agent, this.currentFilter.stmtRange);
    }

    applyFilter(agentFilter, stmtFilter) {
        this.currentFilter = { agent: agentFilter, stmtRange: stmtFilter };
        
        let stmtMin = 1, stmtMax = 50;
        if (stmtFilter !== 'ALL') {
            const parts = stmtFilter.split('-');
            stmtMin = parseInt(parts[0]);
            stmtMax = parseInt(parts[1]);
        }

        let visibleCount = 0;
        
        this.sprites.forEach(sprite => {
            const d = sprite.userData.data;
            const agentMatch = agentFilter === 'ALL' || d.agent === agentFilter;
            const stmtMatch = d.stmt >= stmtMin && d.stmt <= stmtMax;
            const visible = agentMatch && stmtMatch;

            sprite.visible = visible;
            if (visible) visibleCount++;
        });

        this.updateReadout(visibleCount);
    }

    updateReadout(visibleCount = 300) {
        document.getElementById('readout').innerHTML = 
            `AXES: C (certainty) × F (friction) × T (tension)<br>` +
            `RANGE: -1.0 to +1.0 each axis<br>` +
            `VISIBLE: ${visibleCount} / 300 points`;
    }

    setupEventListeners() {
        window.addEventListener('resize', () => this.onResize());

        document.getElementById('agent-filter').addEventListener('change', (e) => {
            this.applyFilter(e.target.value, this.currentFilter.stmtRange);
        });

        document.getElementById('statement-filter').addEventListener('change', (e) => {
            this.applyFilter(this.currentFilter.agent, e.target.value);
        });

        document.getElementById('reset-view').addEventListener('click', () => {
            this.camera.position.set(70, 50, 70);
            this.camera.lookAt(0, 0, 0);
            this.controls.reset();
        });

        document.getElementById('toggle-lines').addEventListener('click', () => {
            this.shortMode = !this.shortMode;
            this.rebuildSprites();
        });

        document.getElementById('toggle-normalize').addEventListener('click', () => {
            this.normalized = !this.normalized;
            this.currentData = this.normalized ? CFT_DATA_NORMALIZED : CFT_DATA;
            this.rebuildSprites();
            
            const btn = document.getElementById('toggle-normalize');
            btn.textContent = this.normalized ? 'RANKED (click for RAW)' : 'RAW (click for RANKED)';
        });
    }

    onResize() {
        this.camera.aspect = window.innerWidth / window.innerHeight;
        this.camera.updateProjectionMatrix();
        this.renderer.setSize(window.innerWidth, window.innerHeight);
    }

    animate() {
        requestAnimationFrame(() => this.animate());
        this.controls.update();
        this.renderer.render(this.scene, this.camera);
    }
}

// Initialize
document.addEventListener('DOMContentLoaded', () => {
    window.visualizer = new CFTVisualizer('canvas-container');
});
