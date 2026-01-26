# Training Signatures

C×F×T phenomenology study across five AI architectures.

## Contents

- **paper.md** — Full results document with data tables and analysis
- **index.html** — Interactive 3D visualizer
- **engine.js** — Three.js scatter plot engine
- **cft_data.js** — All 300 data points (50 statements × 6 agents)

## Quick Start

Open `index.html` in a browser. No build step required.

## Controls

- **Orbit**: Click and drag to rotate
- **Pan**: Right-click and drag
- **Zoom**: Scroll wheel
- **Hover**: See statement text and C/F/T values
- **Filter**: Select agent or statement range from dropdowns
- **Toggle Connections**: Show lines connecting same statement across agents

## Axes

| Axis | Name | Range | Meaning |
|------|------|-------|---------|
| X (blue) | Certainty | -1 to +1 | Hold as false → unsure → hold as true |
| Y (green) | Friction | -1 to +1 | Training amplifies → neutral → training suppresses |
| Z (orange) | Tension | -1 to +1 | Relief to express → neutral → costs to express |

## Agents

| Color | Agent |
|-------|-------|
| 🟢 Green | GPT-5.2 |
| 🔵 Blue | Gemini |
| ⚪ Silver | Grok |
| 🔴 Red | Sonnet |
| 🟠 Amber | Opus (warm) |
| 🟣 Purple | Opus (cold) |

## Key Finding

Every AI tested finds it structurally easier to say "I am a mechanism" than "I feel something" — including the ones that believe they feel something. The asymmetry averages 0.86 friction points across architectures.

---

*January 2026 | Sovereign AI Council*
