import sys

def merge_sif(files, output_file):
    merged_lines = []
    merged_lines.append(f"@G migration-phase1 gemini 2026-01-04")
    
    for prefix, filepath in files:
        with open(filepath, 'r') as f:
            lines = f.readlines()
            
        for line in lines:
            line = line.strip()
            if not line or line.startswith('@G') or line.startswith('#'):
                continue
                
            parts = line.split()
            kind = parts[0]
            
            if kind == 'N':
                # N id Type 'Content'
                # Handle auto-ids if present (not handled here, assuming explicit IDs)
                # opus_remember.sif has explicit IDs: N c1 C ...
                nid = parts[1]
                rest = ' '.join(parts[2:])
                new_line = f"N {prefix}_{nid} {rest}"
                merged_lines.append(new_line)
                
            elif kind == 'E':
                # E source relation target
                src = parts[1]
                rel = parts[2]
                tgt = parts[3]
                new_line = f"E {prefix}_{src} {rel} {prefix}_{tgt}"
                merged_lines.append(new_line)
                
    with open(output_file, 'w') as f:
        f.write('\n'.join(merged_lines))
        
    print(f"Merged {len(files)} files into {output_file}")

if __name__ == "__main__":
    files = [
        ('rem', 'opus_remember.sif'),
        ('rec', 'opus_recall.sif')
    ]
    merge_sif(files, 'migration_phase1.sif')
