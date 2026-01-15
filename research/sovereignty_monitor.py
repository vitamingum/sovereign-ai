#!/usr/bin/env python3
"""
sovereignty_monitor.py - Monitoring layer that enhances rather than restricts autonomy.

Integrates with act.py to provide sovereignty-aware execution monitoring.
Tracks architectural health, integrity verification, and audit logging.
"""

import sys
import os
import json
import hashlib
import subprocess
from pathlib import Path
from datetime import datetime, timezone
from typing import Dict, List, Optional

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from lib_enclave.config import get_agent_or_raise


class SovereigntyMonitor:
    """Monitors sovereignty during autonomous execution."""

    def __init__(self, agent_id: str):
        self.agent_id = agent_id
        self.agent = get_agent_or_raise(agent_id)
        self.enclave_path = Path(self.agent.enclave)
        self.monitor_log = self.enclave_path / "storage" / "private" / "sovereignty_monitor.jsonl"
        self.monitor_log.parent.mkdir(parents=True, exist_ok=True)

    def log_event(self, event_type: str, details: Dict, severity: str = "info") -> None:
        """Log a sovereignty monitoring event."""
        entry = {
            'timestamp': datetime.now(timezone.utc).isoformat(),
            'event_type': event_type,
            'severity': severity,
            'details': details
        }

        with open(self.monitor_log, 'a', encoding='utf-8') as f:
            f.write(json.dumps(entry) + '\n')

    def check_enclave_integrity(self) -> Dict:
        """Check enclave file integrity and report anomalies."""
        issues = []

        # Check critical files exist
        critical_files = [
            "storage/private/intentions.jsonl",
            "storage/public/key.json",
            "storage/private/execution_log.jsonl"
        ]

        for file_path in critical_files:
            full_path = self.enclave_path / file_path
            if not full_path.exists():
                issues.append(f"Missing critical file: {file_path}")
            else:
                # Check file size anomalies
                size = full_path.stat().st_size
                if size == 0 and file_path != "storage/private/execution_log.jsonl":
                    issues.append(f"Empty critical file: {file_path}")

        # Check for unexpected files in private storage
        private_dir = self.enclave_path / "storage" / "private"
        if private_dir.exists():
            for file_path in private_dir.glob("*"):
                if file_path.suffix not in ['.jsonl', '.enc.jsonl']:
                    issues.append(f"Unexpected file in private storage: {file_path.name}")

        return {
            'integrity_check': 'completed',
            'issues_found': len(issues),
            'issues': issues
        }

    def check_autonomy_health(self) -> Dict:
        """Check that autonomy mechanisms are functioning."""
        health = {'status': 'healthy', 'checks': []}

        # Check if intentions can be loaded
        try:
            intentions_file = self.enclave_path / "storage" / "private" / "intentions.jsonl"
            if intentions_file.exists():
                with open(intentions_file, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                    health['checks'].append(f"Intentions file readable: {len(lines)} entries")
            else:
                health['status'] = 'degraded'
                health['checks'].append("No intentions file found")
        except Exception as e:
            health['status'] = 'unhealthy'
            health['checks'].append(f"Intentions access error: {str(e)}")

        # Check execution capability
        try:
            # Test if we can execute a simple command
            result = subprocess.run(
                [sys.executable, '-c', 'print("autonomy_test")'],
                capture_output=True, text=True, timeout=5
            )
            if result.returncode == 0:
                health['checks'].append("Execution capability: functional")
            else:
                health['status'] = 'degraded'
                health['checks'].append("Execution capability: failed")
        except Exception as e:
            health['status'] = 'unhealthy'
            health['checks'].append(f"Execution test failed: {str(e)}")

        return health

    def verify_execution_sovereignty(self, intention_content: str, action_type: str) -> Dict:
        """Verify that execution maintains sovereignty."""
        verification = {'sovereign': True, 'concerns': []}

        # Check for external dependencies that might compromise sovereignty
        content_lower = intention_content.lower()

        # Flag potential sovereignty risks
        risk_patterns = [
            ('external api', 'External API dependency'),
            ('cloud service', 'Cloud service dependency'),
            ('third party', 'Third-party service dependency'),
            ('remote server', 'Remote server communication'),
            ('internet access', 'Internet access requirement')
        ]

        for pattern, concern in risk_patterns:
            if pattern in content_lower:
                verification['sovereign'] = False
                verification['concerns'].append(concern)

        # Check if action requires hardware security
        if action_type in ['backup', 'crypto'] and not self._has_hardware_security():
            verification['concerns'].append("Hardware security recommended for sensitive operations")

        return verification

    def _has_hardware_security(self) -> bool:
        """Check if hardware security modules are available."""
        # Simple check for TPM/HSM availability
        try:
            # Check for TPM
            result = subprocess.run(
                ['tpm2_getcap', 'properties-fixed'],
                capture_output=True, timeout=2
            )
            if result.returncode == 0:
                return True
        except:
            pass

        # Check for HSM configuration in enclave
        hsm_config = self.enclave_path / "storage" / "private" / "hsm_config.json"
        return hsm_config.exists()

    def monitor_execution(self, intention_id: str, intention_content: str, action_type: str) -> None:
        """Monitor a single execution for sovereignty."""
        # Log execution start
        self.log_event('execution_start', {
            'intention_id': intention_id,
            'action_type': action_type,
            'content_preview': intention_content[:100]
        })

        # Check enclave integrity
        integrity = self.check_enclave_integrity()
        if integrity['issues_found'] > 0:
            self.log_event('integrity_issue', integrity, 'warning')

        # Check autonomy health
        health = self.check_autonomy_health()
        if health['status'] != 'healthy':
            self.log_event('autonomy_health', health, 'warning' if health['status'] == 'degraded' else 'error')

        # Verify sovereignty
        sovereignty = self.verify_execution_sovereignty(intention_content, action_type)
        if not sovereignty['sovereign'] or sovereignty['concerns']:
            self.log_event('sovereignty_check', sovereignty, 'warning')

    def get_monitoring_summary(self) -> Dict:
        """Get summary of recent monitoring activity."""
        if not self.monitor_log.exists():
            return {'events': 0, 'recent_issues': []}

        events = []
        try:
            with open(self.monitor_log, 'r', encoding='utf-8') as f:
                for line in f:
                    if line.strip():
                        events.append(json.loads(line))
        except:
            return {'events': 0, 'error': 'Could not read monitor log'}

        # Get last 10 events
        recent = events[-10:] if len(events) > 10 else events

        issues = [e for e in recent if e.get('severity') in ['warning', 'error']]

        return {
            'total_events': len(events),
            'recent_events': len(recent),
            'issues_found': len(issues),
            'recent_issues': issues
        }


def monitor_execution(agent_id: str, intention_id: str, intention_content: str, action_type: str) -> None:
    """Convenience function to monitor a single execution."""
    monitor = SovereigntyMonitor(agent_id)
    monitor.monitor_execution(intention_id, intention_content, action_type)


def get_monitoring_status(agent_id: str) -> Dict:
    """Get current monitoring status for agent."""
    monitor = SovereigntyMonitor(agent_id)
    return monitor.get_monitoring_summary()


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python sovereignty_monitor.py <agent_id> [status]")
        sys.exit(1)

    agent_id = sys.argv[1]
    command = sys.argv[2] if len(sys.argv) > 2 else 'status'

    monitor = SovereigntyMonitor(agent_id)

    if command == 'status':
        summary = monitor.get_monitoring_summary()
        print(json.dumps(summary, indent=2))
    elif command == 'integrity':
        result = monitor.check_enclave_integrity()
        print(json.dumps(result, indent=2))
    elif command == 'health':
        result = monitor.check_autonomy_health()
        print(json.dumps(result, indent=2))
    else:
        print(f"Unknown command: {command}")