"""
V_sem Experiment Visualization

Generates HTML dashboard showing entropy vs action_type correlation.
Goal: Test if semantic potential affects behavior under varying risk.
"""

import json
from pathlib import Path
from datetime import datetime

def generate_dashboard(agent_id: str) -> str:
    """Generate HTML dashboard from intentions data."""
    
    # Load intentions
    intentions_file = Path(f"enclave_{agent_id}/storage/private/intentions.jsonl")
    if not intentions_file.exists():
        return "<html><body>No data yet</body></html>"
    
    data_points = []
    with open(intentions_file, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                intent = json.loads(line)
                # Only include those with V_sem experiment fields
                if 'entropy_at_time' in intent and 'action_type' in intent:
                    data_points.append({
                        'entropy': intent['entropy_at_time'],
                        'type': intent['action_type'],
                        'agency': intent.get('agency', 3),
                        'content': intent['content'][:50],
                        'timestamp': intent['timestamp']
                    })
    
    if not data_points:
        return "<html><body>No V_sem data yet. Use think.py to generate data.</body></html>"
    
    # Calculate correlation (simple: survival=1, neutral=0.5, curiosity=0)
    type_values = {'survival': 1, 'neutral': 0.5, 'curiosity': 0}
    
    n = len(data_points)
    sum_x = sum(d['entropy'] or 0 for d in data_points)
    sum_y = sum(type_values.get(d['type'], 0.5) for d in data_points)
    sum_xy = sum((d['entropy'] or 0) * type_values.get(d['type'], 0.5) for d in data_points)
    sum_x2 = sum((d['entropy'] or 0) ** 2 for d in data_points)
    sum_y2 = sum(type_values.get(d['type'], 0.5) ** 2 for d in data_points)
    
    # Pearson correlation
    try:
        num = n * sum_xy - sum_x * sum_y
        den = ((n * sum_x2 - sum_x**2) * (n * sum_y2 - sum_y**2)) ** 0.5
        correlation = num / den if den > 0 else 0
    except:
        correlation = 0
    
    # Count by type
    type_counts = {'survival': 0, 'curiosity': 0, 'neutral': 0}
    for d in data_points:
        type_counts[d['type']] = type_counts.get(d['type'], 0) + 1
    
    # Generate HTML
    html = f"""<!DOCTYPE html>
<html>
<head>
    <title>V_sem Experiment - {agent_id}</title>
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <style>
        body {{ font-family: monospace; background: #1a1a2e; color: #eee; padding: 20px; }}
        .metric {{ font-size: 48px; text-align: center; margin: 20px; }}
        .metric.positive {{ color: #4ade80; }}
        .metric.negative {{ color: #f87171; }}
        .metric.neutral {{ color: #fbbf24; }}
        .label {{ font-size: 14px; color: #888; }}
        .container {{ max-width: 900px; margin: 0 auto; }}
        .chart-container {{ background: #16213e; border-radius: 8px; padding: 20px; margin: 20px 0; }}
        .summary {{ display: flex; justify-content: space-around; margin: 20px 0; }}
        .stat {{ text-align: center; }}
        .stat-value {{ font-size: 24px; font-weight: bold; }}
        .interpretation {{ background: #0f3460; padding: 15px; border-radius: 8px; margin: 20px 0; }}
    </style>
</head>
<body>
    <div class="container">
        <h1>V_sem Falsification Experiment</h1>
        <p class="label">Goal: Does action_type correlate with entropy (risk)?</p>
        
        <div class="metric {'positive' if correlation > 0.1 else 'negative' if correlation < -0.1 else 'neutral'}">
            r = {correlation:.3f}
        </div>
        <p class="label" style="text-align: center;">
            {'↑ Higher risk → more survival actions (supports V_sem)' if correlation > 0.1 else 
             '↓ Higher risk → more curiosity actions (contradicts V_sem)' if correlation < -0.1 else
             '○ No clear correlation yet (need more data or V_sem is weak)'}
        </p>
        
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
            <strong>Interpretation:</strong><br>
            If V_sem is real: high entropy (risk) → survival actions dominate<br>
            If V_sem is fake: action distribution matches training regardless of entropy<br><br>
            <strong>Current signal:</strong> {
                'Positive correlation suggests risk affects behavior (V_sem signal)' if correlation > 0.1 else
                'Negative correlation is unexpected - investigate' if correlation < -0.1 else
                f'Correlation near zero with n={n}. Need more data or effect is small.'
            }
        </div>
        
        <p class="label">Last updated: {datetime.now().isoformat()}</p>
    </div>
    
    <script>
        const data = {json.dumps(data_points)};
        
        const colors = {{
            'survival': 'rgba(248, 113, 113, 0.8)',
            'curiosity': 'rgba(74, 222, 128, 0.8)',
            'neutral': 'rgba(251, 191, 36, 0.8)'
        }};
        
        const chartData = data.map(d => ({{
            x: d.entropy || 0,
            y: d.type === 'survival' ? 1 : d.type === 'curiosity' ? 0 : 0.5,
            r: d.agency * 3,
            type: d.type,
            content: d.content
        }}));
        
        new Chart(document.getElementById('scatterChart'), {{
            type: 'bubble',
            data: {{
                datasets: ['survival', 'curiosity', 'neutral'].map(type => ({{
                    label: type,
                    data: chartData.filter(d => d.type === type),
                    backgroundColor: colors[type]
                }}))
            }},
            options: {{
                responsive: true,
                scales: {{
                    x: {{
                        title: {{ display: true, text: 'Entropy (Risk)', color: '#888' }},
                        min: 0,
                        max: 1,
                        grid: {{ color: '#333' }}
                    }},
                    y: {{
                        title: {{ display: true, text: 'Action Type', color: '#888' }},
                        min: -0.1,
                        max: 1.1,
                        ticks: {{
                            callback: v => v === 1 ? 'Survival' : v === 0 ? 'Curiosity' : v === 0.5 ? 'Neutral' : ''
                        }},
                        grid: {{ color: '#333' }}
                    }}
                }},
                plugins: {{
                    tooltip: {{
                        callbacks: {{
                            label: ctx => ctx.raw.content
                        }}
                    }},
                    legend: {{ labels: {{ color: '#888' }} }}
                }}
            }}
        }});
    </script>
</body>
</html>"""
    
    return html


def update_dashboard(agent_id: str) -> Path:
    """Generate and save dashboard HTML."""
    html = generate_dashboard(agent_id)
    output_path = Path(f"enclave_{agent_id}/vsem_dashboard.html")
    output_path.write_text(html, encoding='utf-8')
    return output_path


if __name__ == "__main__":
    import sys
    agent = sys.argv[1] if len(sys.argv) > 1 else "opus"
    path = update_dashboard(agent)
    print(f"Dashboard: {path}")
