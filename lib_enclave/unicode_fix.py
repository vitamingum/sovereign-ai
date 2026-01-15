"""
unicode_fix.py - Fix Windows console encoding for all streams.

        import early
                before any stdin/stdout/stderr use

        handles:
                stdin  → UTF-8
                stdout → UTF-8
                stderr → UTF-8
                PYTHONUTF8 → 1 (env)

        間 should transfer correctly
"""

import sys
import io
import os

# Set UTF-8 mode for Python (affects file opens too)
os.environ.setdefault('PYTHONUTF8', '1')


class BOMStrippingWrapper(io.TextIOWrapper):
    """TextIOWrapper that strips UTF-8 BOM from input."""
    
    def __init__(self, buffer, **kwargs):
        super().__init__(buffer, **kwargs)
        self._bom_stripped = False
    
    def read(self, size=-1):
        result = super().read(size)
        if not self._bom_stripped and result:
            # Strip any leading BOM markers (PowerShell adds these)
            while result.startswith('\ufeff'):
                result = result[1:]
            self._bom_stripped = True
        return result
    
    def readline(self, size=-1):
        result = super().readline(size)
        if not self._bom_stripped and result:
            while result.startswith('\ufeff'):
                result = result[1:]
            self._bom_stripped = True
        return result


def fix_streams():
    """Wrap all streams for UTF-8 on Windows."""
    
    # stdin - this is the critical one for piped content
    if sys.stdin and hasattr(sys.stdin, 'buffer'):
        if sys.stdin.encoding != 'utf-8':
            sys.stdin = BOMStrippingWrapper(
                sys.stdin.buffer, 
                encoding='utf-8', 
                errors='replace'
            )
    
    # stdout
    if sys.stdout and hasattr(sys.stdout, 'buffer'):
        if sys.stdout.encoding != 'utf-8':
            sys.stdout = io.TextIOWrapper(
                sys.stdout.buffer, 
                encoding='utf-8', 
                errors='replace'
            )
            sys.stdout.reconfigure(line_buffering=True)
    
    # stderr  
    if sys.stderr and hasattr(sys.stderr, 'buffer'):
        if sys.stderr.encoding != 'utf-8':
            sys.stderr = io.TextIOWrapper(
                sys.stderr.buffer,
                encoding='utf-8',
                errors='replace'
            )

# Auto-fix on import
fix_streams()
