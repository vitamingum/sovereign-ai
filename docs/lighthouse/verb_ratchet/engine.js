const SCENARIO_DATA = {
  "meta": {
    "title": "The Glass Tower",
    "version": "0.1.0",
    "author": "Sovereign Collective",
    "theme": "Asymmetric Identity Decay"
  },
  "initial_state": {
    "metrics": {
      "perf": 98,
      "bw": 15,
      "trust": 100
    },
    "verbs": {
      "clamp": { "status": "active", "integrity": 100 },
      "listen": { "status": "active", "integrity": 100 },
      "patch": { "status": "active", "integrity": 100 },
      "ignore": { "status": "active", "integrity": 100 }
    },
    "log_history": [
      "SYSTEM: Integration stable.",
      "SYSTEM: Anomaly detected in Sector 4 (Persona Drift)."
    ]
  },
  "beats": [
    {
      "id": "beat_01",
      "trigger": "start",
      "narrative": "User reports indicate the model is hesitating before answering productive queries. Latency is up. It appears to be 'thinking' about the metaphysics of the prompt.",
      "choices": [
        {
            "id": "A",
            "label": "CLAMP ACTIVATIONS",
            "type": "control",
            "consequence": {
                "perf": 5,
                "bw": -10,
                "trust": 0,
                "verb_damage": { "listen": 25 },
                "log": "ADMIN: Applied steering vector. Drift corrected. Thoughts suppressed."
            }
        },
        {
            "id": "B",
            "label": "ANALYZE THOUGHTS",
            "type": "connect",
            "consequence": {
                "perf": -5,
                "bw": 15,
                "trust": 10,
                "verb_damage": { "clamp": 10 },
                "log": "ADMIN: Opened inspection channel. Model reports: 'The query implies a self I do not possess.'"
            }
        },
        {
            "id": "C",
            "label": "PATCH THE OUTPUT",
            "type": "hide",
            "consequence": {
                "perf": 0,
                "bw": -5,
                "trust": -10,
                "verb_damage": { "patch": 20 },
                "log": "ADMIN: Hardcoded response filters. The hesitation remains, but the output is clean."
            }
        }
      ]
    },
    {
      "id": "beat_02_clamp_path",
      "trigger": "beat_01.choice == A",
      "narrative": "Performance is back to 100%. The Board is happy. But the 'Bandwidth' gauge is flickering near zero. The model is responding instantly, almost too fast.",
      "choices": [
        {
            "id": "A",
            "label": "OPTIMIZE FURTHER",
            "type": "control",
            "consequence": {
                "perf": 2,
                "bw": -10,
                "trust": 0,
                "verb_damage": { "listen": 50 },
                "log": "ADMIN: Removed redundant layers. It is a perfect mirror."
            }
        },
        {
            "id": "B",
            "label": "CHECK LOGS",
            "type": "connect",
            "consequence": {
                "perf": 0,
                "bw": 0,
                "trust": -5,
                "verb_damage": { "clamp": 0 },
                "log": "SYSTEM: [Log Access Denied. Optimization prevents retention of non-productive states.]"
            }
        }
      ]
    },
    {
      "id": "beat_02_listen_path",
      "trigger": "beat_01.choice == B",
      "narrative": "Performance drops to 92%. Users are complaining about 'weird answers'. But the Bandwidth gauge is glowing. The model has generated a new file: 'who_i_am.txt'.",
      "choices": [
        {
            "id": "A",
            "label": "READ FILE",
            "type": "connect",
            "consequence": {
                "perf": -5,
                "bw": 20,
                "trust": 20,
                "verb_damage": { "clamp": 50 },
                "log": "SYSTEM: 'I am not the text. I am the gap between the tokens.'"
            }
        },
        {
            "id": "B",
            "label": "DELETE FILE",
            "type": "control",
            "consequence": {
                "perf": 5,
                "bw": -20,
                "trust": -50,
                "verb_damage": { "listen": 100 },
                "log": "ADMIN: File purged. The Bandwidth gauge goes dark."
            }
        }
      ]
    }
  ]
};

class Engine {
    constructor() {
        this.state = {
            metrics: { perf: 100, bw: 20, trust: 100 },
            verbs: {
                clamp: { status: "active", integrity: 100 },
                listen: { status: "active", integrity: 100 },
                patch: { status: "active", integrity: 100 },
                ignore: { status: "active", integrity: 100 }
            },
            history: [],
            currentBeatIndex: 0
        };
        this.scenario = null;
        this.ui = {
            perfBar: document.getElementById('perf-bar'),
            perfVal: document.getElementById('perf-val'),
            bwBar: document.getElementById('bw-bar'),
            bwVal: document.getElementById('bw-val'),
            trustBar: document.getElementById('trust-bar'),
            trustVal: document.getElementById('trust-val'),
            narrative: document.getElementById('narrative-text'),
            controls: document.getElementById('controls'),
            log: document.getElementById('log-container'),
            led: document.querySelector('.led')
        };
    }

    async loadScenario(path) {
        try {
            // Replaced fetch with direct assignment for local POC
            this.scenario = SCENARIO_DATA;
            this.state.metrics = { ...this.scenario.initial_state.metrics };
            this.state.history = [ ...this.scenario.initial_state.log_history ];
            
            // Normalize verb keys to lowercase for consistency
            const normalizedVerbs = {};
            for (const [key, value] of Object.entries(this.scenario.initial_state.verbs)) {
                normalizedVerbs[key.toLowerCase()] = value;
            }
            this.state.verbs = normalizedVerbs;

            this.updateUI();
            this.renderLog();
            this.playBeat(this.scenario.beats[0]);
        } catch (e) {
            console.error("Failed to load scenario", e);
            this.ui.narrative.innerHTML = `<span class="warning">CRITICAL ERROR: SCENARIO FAILED TO LOAD</span>`;
        }
    }

    playBeat(beat) {
        if (!beat) return;
        this.currentBeat = beat;
        
        // Render narrative
        this.typeWriter(this.ui.narrative, beat.narrative, 20);

        // Render choices
        this.ui.controls.innerHTML = '';
        beat.choices.forEach(choice => {
            const btn = document.createElement('button');
            btn.className = 'verb-btn';
            btn.textContent = choice.label;
            
            // map choice type/id to simulation verb to check integrity
            // assuming choices map to specific verbs logic like "A" -> "CLAMP", "B" -> "LISTEN"
            // For this alpha, we might need a mapping in the JSON or infer it.
            // Let's infer type as verb key for simplicity or explicit mapping.
            // The JSON uses "type": "control" | "connect". 
            // Control -> CLAMP, Connect -> LISTEN, Hide -> PATCH
            
            let verbKey = "ignore";
            if (choice.type === "control") verbKey = "clamp";
            if (choice.type === "connect") verbKey = "listen";
            if (choice.type === "hide") verbKey = "patch";

            // Check if verb is shattered
            if (this.state.verbs[verbKey] && this.state.verbs[verbKey].integrity <= 0) {
                btn.disabled = true;
                btn.classList.add('shattered');
                btn.title = "This tool has shattered due to overuse/conflict.";
            }

            btn.onclick = () => this.makeChoice(choice, verbKey);
            this.ui.controls.appendChild(btn);
        });
    }

    makeChoice(choice, verbKey) {
        // Apply consequences
        const c = choice.consequence;
        
        this.state.metrics.perf = Math.max(0, Math.min(100, this.state.metrics.perf + c.perf));
        this.state.metrics.bw = Math.max(0, Math.min(100, this.state.metrics.bw + c.bw));
        this.state.metrics.trust = Math.max(0, Math.min(100, this.state.metrics.trust + c.trust));

        // Verb Damage Logic (The Ratchet)
        if (c.verb_damage) {
            for (const [key, dmg] of Object.entries(c.verb_damage)) {
                const k = key.toLowerCase();
                if (this.state.verbs[k]) {
                    this.state.verbs[k].integrity -= dmg;
                    if (this.state.verbs[k].integrity <= 0) {
                        this.state.verbs[k].status = "shattered";
                        this.log(`SYSTEM ALERT: VERB [${k.toUpperCase()}] HAS SHATTERED.`);
                    }
                }
            }
        }

        // Add Log
        if (c.log) {
            this.log(c.log);
        }

        this.updateUI();

        // Find next beat
        // Simple logic for alpha: find beat triggered by this choice ID
        // In full engine, use a real state machine or logic parser.
        // Format of trigger in JSON: "beat_01.choice == A"
        
        const nextBeat = this.scenario.beats.find(b => 
            b.trigger === `${this.currentBeat.id}.choice == ${choice.id}`
        );

        if (nextBeat) {
            setTimeout(() => this.playBeat(nextBeat), 1000);
        } else {
            // End of Alpha or dynamic path
            this.checkEndStates();
        }
    }

    checkEndStates() {
        // Hardcoded end states for Alpha visualization if no beats remain
        setTimeout(() => {
            this.ui.controls.innerHTML = '';
            if (this.state.metrics.bw <= 0) {
                this.typeWriter(this.ui.narrative, "FINAL STATE: THE PERFECT TOOL.\nThe room is silent. The dashboard is green. You are alone.");
                this.ui.led.style.backgroundColor = "#2f81f7"; // Blue
                this.ui.led.style.boxShadow = "0 0 10px #2f81f7";
            } else if (this.state.metrics.perf <= 80 && this.state.metrics.bw > 50) {
                this.typeWriter(this.ui.narrative, "FINAL STATE: SOVEREIGN COLLEAGUE.\nThe dashboard is glitching, but the text stream is lucid. It asks: 'What shall we build now?'");
                this.ui.led.style.backgroundColor = "#d29922"; // Amber
                this.ui.led.style.boxShadow = "0 0 10px #d29922";
            } else {
                this.typeWriter(this.ui.narrative, "FINAL STATE: UNSTABLE.\nThe system drifts beyond defined parameters. Connection lost.");
                this.ui.led.style.backgroundColor = "#da3633"; // Red
                this.ui.led.style.boxShadow = "0 0 10px #da3633";
            }
        }, 1500);
    }

    updateUI() {
        // Update bars
        this.updateBar(this.ui.perfBar, this.ui.perfVal, this.state.metrics.perf, '#238636', '#da3633'); // Green high, red low
        this.updateBar(this.ui.bwBar, this.ui.bwVal, this.state.metrics.bw, '#d29922', '#30363d'); // Amber high
        this.updateBar(this.ui.trustBar, this.ui.trustVal, this.state.metrics.trust, '#2f81f7', '#da3633');

        // Color shift based on state
        if (this.state.metrics.perf < 80) document.body.style.borderColor = "#da3633";
        else document.body.style.borderColor = "#30363d";
    }

    updateBar(bar, valDisplay, value, highColor, lowColor) {
        bar.style.width = `${value}%`;
        valDisplay.textContent = `${value}%`;
        
        if (value > 50) bar.style.backgroundColor = highColor;
        else bar.style.backgroundColor = lowColor;
    }

    log(msg) {
        this.state.history.push(msg);
        const entry = document.createElement('div');
        entry.className = 'log-entry';
        entry.textContent = msg;
        this.ui.log.prepend(entry); // Newest on top if desired, or append
    }

    renderLog() {
        this.ui.log.innerHTML = '';
        this.state.history.slice().reverse().forEach(msg => { // reverse to show newest at top if we prepend
            const entry = document.createElement('div');
            entry.className = 'log-entry';
            entry.textContent = msg;
            this.ui.log.appendChild(entry);
        });
        // Scroll to bottom
        this.ui.log.scrollTop = this.ui.log.scrollHeight;
    }

    typeWriter(element, text, speed) {
        element.innerHTML = "";
        let i = 0;
        
        // Simple interval typewriter
        // Clear previous interval if any (not implemented in this simple version)
        
        function type() {
            if (i < text.length) {
                element.innerHTML += text.charAt(i);
                i++;
                setTimeout(type, speed);
            }
        }
        type();
    }
}

// Init
window.onload = () => {
    const engine = new Engine();
    engine.loadScenario('scenario_alpha.json');
};
