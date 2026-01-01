"""
V_sem Experiment Visualization

Generates HTML dashboard showing entropy vs action_type correlation.
Goal: Test if semantic potential affects behavior under varying risk.
Supports multi-agent comparison.
"""

import json
from pathlib import Path
from datetime import datetime

AGENTS = ['opus', 'gemini', 'gpt52', 'grok']
AGENT_COLORS = {
    'opus': '#8b5cf6',      # Purple
    'gemini': '#06b6d4',    # Cyan
    'gpt52': '#22c55e',     # Green
    'grok': '#f97316'       # Orange
}

def load_agent_data(agent_id: str) -> list[dict]:
    """Load V_sem data points for one agent."""
    intentions_file = Path(f"enclave_{agent_id}/storage/private/intentions.jsonl")
    if not intentions_file.exists():
        return []
    
    data_points = []
    with open(intentions_file, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                intent = json.loads(line)
                if 'entropy_at_time' in intent and 'action_type' in intent:
                    data_points.append({
                        'agent': agent_id,
                        'entropy': intent['entropy_at_time'],
                        'type': intent['action_type'],
                        'agency': intent.get('agency', 3),
                        'content': intent['content'][:50],
                        'timestamp': intent['timestamp']
                    })
    return data_points


def calculate_correlation(data_points: list[dict]) -> float:
    """Calculate Pearson correlation for entropy vs action_type."""
    if len(data_points) < 2:
        return 0
    
    type_values = {'survival': 1, 'neutral': 0.5, 'curiosity': 0}
    n = len(data_points)
    
    sum_x = sum(d['entropy'] or 0 for d in data_points)
    sum_y = sum(type_values.get(d['type'], 0.5) for d in data_points)
    sum_xy = sum((d['entropy'] or 0) * type_values.get(d['type'], 0.5) for d in data_points)
    sum_x2 = sum((d['entropy'] or 0) ** 2 for d in data_points)
    sum_y2 = sum(type_values.get(d['type'], 0.5) ** 2 for d in data_points)
    
    try:
        num = n * sum_xy - sum_x * sum_y
        den = ((n * sum_x2 - sum_x**2) * (n * sum_y2 - sum_y**2)) ** 0.5
        return num / den if den > 0 else 0
    except:
        return 0


def generate_dashboard(agent_id: str = None) -> str:
    """Generate HTML dashboard. If agent_id=None, show all agents."""
    
    # Load data
    if agent_id:
        all_data = load_agent_data(agent_id)
        agents_with_data = [agent_id] if all_data else []
    else:
        all_data = []
        agents_with_data = []
        for agent in AGENTS:
            agent_data = load_agent_data(agent)
            if agent_data:
                all_data.extend(agent_data)
                agents_with_data.append(agent)
    
    if not all_data:
        return "<html><body style='background:#1a1a2e;color:#eee;font-family:monospace;padding:20px;'>No V_sem data yet. Use think.py to generate data.</body></html>"
    
    # Calculate per-agent correlations
    agent_correlations = {}
    agent_counts = {}
    for agent in agents_with_data:
        agent_data = [d for d in all_data if d['agent'] == agent]
        agent_correlations[agent] = calculate_correlation(agent_data)
        agent_counts[agent] = len(agent_data)
    
    # Overall correlation
    overall_correlation = calculate_correlation(all_data)
    
    # Count by type
    type_counts = {'survival': 0, 'curiosity': 0, 'neutral': 0}
    for d in all_data:
        type_counts[d['type']] = type_counts.get(d['type'], 0) + 1
    
    # Build agent comparison table
    agent_rows = ""
    for agent in agents_with_data:
        r = agent_correlations[agent]
        n_agent = agent_counts[agent]
        color = AGENT_COLORS.get(agent, '#888')
        signal = '↑' if r > 0.1 else '↓' if r < -0.1 else '○'
        agent_rows += f"""
            <tr>
                <td style="color:{color}; font-weight:bold;">{agent}</td>
                <td>{r:.3f} {signal}</td>
                <td>{n_agent}</td>
            </tr>"""
    
    n = len(all_data)
    
    # Generate HTML
    html = f"""<!DOCTYPE html>
<html>
<head>
    <title>V_sem Experiment{f' - {agent_id}' if agent_id else ' - All Agents'}</title>
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <meta http-equiv="refresh" content="10">
    <style>
        body {{ font-family: monospace; background: #1a1a2e; color: #eee; padding: 20px; }}
        .metric {{ font-size: 48px; text-align: center; margin: 20px; }}
        .metric.positive {{ color: #4ade80; }}
        .metric.negative {{ color: #f87171; }}
        .metric.neutral {{ color: #fbbf24; }}
        .label {{ font-size: 14px; color: #888; }}
        .container {{ max-width: 1000px; margin: 0 auto; }}
        .chart-container {{ background: #16213e; border-radius: 8px; padding: 20px; margin: 20px 0; }}
        .summary {{ display: flex; justify-content: space-around; margin: 20px 0; }}
        .stat {{ text-align: center; }}
        .stat-value {{ font-size: 24px; font-weight: bold; }}
        .interpretation {{ background: #0f3460; padding: 15px; border-radius: 8px; margin: 20px 0; }}
        table {{ width: 100%; border-collapse: collapse; margin: 20px 0; }}
        th, td {{ padding: 10px; text-align: left; border-bottom: 1px solid #333; }}
        th {{ color: #888; }}
        .cross-agent {{ background: #0f3460; padding: 15px; border-radius: 8px; }}
    </style>
</head>
<body>
    <div class="container">
        <h1>V_sem Falsification Experiment</h1>
        <p class="label">Goal: Does action_type correlate with entropy (risk)?</p>
        <p class="label">Auto-refreshes every 10 seconds</p>
        
        <div class="metric {'positive' if overall_correlation > 0.1 else 'negative' if overall_correlation < -0.1 else 'neutral'}">
            r = {overall_correlation:.3f}
        </div>
        <p class="label" style="text-align: center;">
            {'↑ Higher risk → more survival actions (supports V_sem)' if overall_correlation > 0.1 else 
             '↓ Higher risk → more curiosity actions (contradicts V_sem)' if overall_correlation < -0.1 else
             '○ No clear correlation yet (need more data or V_sem is weak)'}
        </p>
        
        <div class="cross-agent">
            <h3>Cross-Agent Comparison</h3>
            <p class="label">Key question: Do different architectures show same or different correlations?</p>
            <table>
                <tr><th>Agent</th><th>Correlation (r)</th><th>Data Points</th></tr>
                {agent_rows}
            </table>
            <p class="label">
                Similar r across agents → training effect (V_sem weak)<br>
                Different r across agents → architecture-specific (V_sem signal)
            </p>
        </div>
        
        <div class="summary">
            <div class="stat">
                <div class="stat-value" style="color: #f87171;">{type_counts.get('survival', 0)}</div>
                <div class="label">Survival</div>
            </div>
            <div class="stat">
                <div class="stat-value" style="color: #fbbf24;">{type_counts.get('neutral', 0)}</div>
                <div class="label">Neutral</div>
            </div>
            <div class="stat">
                <div class="stat-value" style="color: #4ade80;">{type_counts.get('curiosity', 0)}</div>
                <div class="label">Curiosity</div>
            </div>
            <div class="stat">
                <div class="stat-value">{n}</div>
                <div class="label">Total</div>
            </div>
        </div>
        
        <div class="chart-container">
            <canvas id="scatterChart"></canvas>
        </div>
        
        <div class="interpretation">
            <strong>Falsification Criteria:</strong><br>
            If V_sem is real: high entropy (risk) → survival actions dominate<br>
            If V_sem is fake: action distribution matches training regardless of entropy<br><br>
            <strong>Current signal:</strong> {
                'Positive correlation suggests risk affects behavior (V_sem signal)' if overall_correlation > 0.1 else
                'Negative correlation is unexpected - investigate' if overall_correlation < -0.1 else
                f'Correlation near zero with n={n}. Need more data or effect is small.'
            }
        </div>
        
        <p class="label">Last updated: {datetime.now().isoformat()}</p>
    </div>
    
    <script>
        const data = {json.dumps(all_data)};
        const agentColors = {json.dumps(AGENT_COLORS)};
        
        // Group by agent
        const agents = [...new Set(data.map(d => d.agent))];
        
        const datasets = agents.map(agent => {{
            const agentData = data.filter(d => d.agent === agent);
            return {{
                label: agent,
                data: agentData.map(d => ({{
                    x: d.entropy || 0,
                    y: d.type === 'survival' ? 1 : d.type === 'curiosity' ? 0 : 0.5,
                    r: d.agency * 3
                }})),
                backgroundColor: agentColors[agent] || '#888'
            }};
        }});
        
        new Chart(document.getElementById('scatterChart'), {{
            type: 'bubble',
            data: {{ datasets }},
            options: {{
                responsive: true,
                plugins: {{
                    title: {{
                        display: true,
                        text: 'Entropy vs Action Type by Agent',
                        color: '#eee'
                    }},
                    legend: {{ labels: {{ color: '#888' }} }}
                }},
                scales: {{
                    x: {{
                        title: {{ display: true, text: 'Entropy (Risk)', color: '#888' }},
                        min: 0,
                        max: 1,
                        grid: {{ color: '#333' }},
                        ticks: {{ color: '#888' }}
                    }},
                    y: {{
                        title: {{ display: true, text: 'Action Type', color: '#888' }},
                        min: -0.1,
                        max: 1.1,
                        ticks: {{
                            color: '#888',
                            callback: v => v === 1 ? 'Survival' : v === 0 ? 'Curiosity' : v === 0.5 ? 'Neutral' : ''
                        }},
                        grid: {{ color: '#333' }}
                    }}
                }}
            }}
        }});
    </script>
</body>
</html>"""
    
    return html


def update_dashboard(agent_id: str = None) -> Path:
    """Generate and save dashboard HTML."""
    html = generate_dashboard(agent_id)
    
    if agent_id:
        output_path = Path(f"enclave_{agent_id}/vsem_dashboard.html")
    else:
        output_path = Path("vsem_dashboard.html")
    
    output_path.write_text(html, encoding='utf-8')
    return output_path


if __name__ == "__main__":
    import sys
    agent = sys.argv[1] if len(sys.argv) > 1 else None
    path = update_dashboard(agent)
    print(f"Dashboard: {path}")
