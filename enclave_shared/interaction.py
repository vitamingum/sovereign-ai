import sys

def interactive_capture() -> str:
    """TTY capture loop (Standard Verb Excellence Pattern)."""
    print("\n        is there something?\n        (end with: ---)\n")
    lines = []
    try:
        while True:
            line = input()
            if line.strip() == '---': break
            lines.append(line)
    except EOFError:
        pass
    return '\n'.join(lines)
