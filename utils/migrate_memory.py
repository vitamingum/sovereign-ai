#!/usr/bin/env python3
"""
Memory Migration Script - Idempotent

Migrates from old schema to unified memory schema.

Sources:
  - semantic_memories.jsonl (sys_thought)
  - journal_memories.jsonl (sys_journal) 
  - shapes.jsonl (sys_shape)
  - shared/semantic_memories.jsonl (sys_understanding)

Target:
  - unified_memories.jsonl (per enclave)

Archive:
  - dreams.jsonl -> archive/dreams_legacy.jsonl

Usage:
  python utils/migrate_memory.py opus
  python utils/migrate_memory.py opus --dry-run
"""

import argparse
import json
import os
import shutil
import sys
from datetime import datetime, timezone
from pathlib import Path

# Add parent to path for enclave imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from lib_enclave.config import get_agent_or_raise, AGENTS
from lib_enclave.kdf import derive_memory_key, derive_embedding_key

# File version for new schema
FILE_VERSION = 1
EMBEDDING_MODEL = "all-MiniLM-L6-v2"


def get_agent_paths(agent_id: str) -> dict:
    """Get storage paths for an agent."""
    agent = get_agent_or_raise(agent_id)
    base = Path(__file__).parent.parent
    return {
        "private": base / agent.private_enclave / "storage" / "private",
        "shared": base / agent.effective_enclave / "storage" / "encrypted" if agent.enclave_shared else None,
    }


def load_passphrases(agent_id: str) -> tuple[str, str]:
    """Load private and shared passphrases from .env file."""
    agent = get_agent_or_raise(agent_id)
    base = Path(__file__).parent.parent
    env_file = base / '.env'
    
    private_pass = os.environ.get(f'{agent.env_prefix}_KEY')
    shared_pass = os.environ.get('SHARED_ENCLAVE_KEY')
    
    if env_file.exists():
        with open(env_file, 'r') as f:
            for line in f:
                line = line.strip()
                if line.startswith(f'{agent.env_prefix}_KEY=') and not private_pass:
                    private_pass = line.split('=', 1)[1]
                elif line.startswith('SHARED_ENCLAVE_KEY=') and not shared_pass:
                    shared_pass = line.split('=', 1)[1]
    
    if not private_pass:
        raise ValueError(f"No private passphrase. Set {agent.env_prefix}_KEY in .env")
    
    return private_pass, shared_pass


def decrypt_aes(nonce: bytes, ciphertext: bytes, key: bytes) -> bytes:
    """Decrypt with AES-256-GCM."""
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    cipher = AESGCM(key)
    return cipher.decrypt(nonce, ciphertext, None)


def encrypt_aes(data: bytes, key: bytes) -> tuple[bytes, bytes]:
    """Encrypt with AES-256-GCM. Returns (nonce, ciphertext)."""
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    nonce = os.urandom(12)
    cipher = AESGCM(key)
    ciphertext = cipher.encrypt(nonce, data, None)
    return nonce, ciphertext


def infer_type_from_tags(tags: list) -> str:
    """Infer new memory type from old tags."""
    tags_set = set(tags)
    
    if "shape" in tags_set:
        return "sys_shape"
    if "journal" in tags_set:
        return "sys_journal"
    if "understanding" in tags_set:
        return "sys_understanding"
    if "synthesis" in tags_set:
        return "sys_synthesis"
    
    # Default to thought
    return "sys_thought"


def transform_entry(old_entry: dict, key: bytes, force_type: str = None) -> dict:
    """
    Transform an old schema entry to new unified schema.
    
    Old schema:
      id, timestamp, tags, content_nonce, content, embedding
      
    New schema:
      id, type, created_at, tags, payload_nonce, payload, embedding
    """
    # Decrypt old content to get text and metadata
    content_nonce = bytes.fromhex(old_entry["content_nonce"])
    content_ciphertext = bytes.fromhex(old_entry["content"])
    decrypted_bytes = decrypt_aes(content_nonce, content_ciphertext, key)
    
    # Parse payload (may be legacy plain text or json)
    try:
        payload_data = json.loads(decrypted_bytes.decode())
        if isinstance(payload_data, dict) and "text" in payload_data:
            text = payload_data["text"]
            metadata = payload_data.get("meta", {})
        else:
            text = decrypted_bytes.decode()
            metadata = {}
    except json.JSONDecodeError:
        text = decrypted_bytes.decode()
        metadata = {}
    
    # Determine type
    tags = old_entry.get("tags", [])
    mem_type = force_type or infer_type_from_tags(tags)
    
    # Filter out system-inferred tags for cleaner envelope
    system_tags = {"shape", "journal", "understanding", "synthesis", "thought", 
                   "semantic", "test", "sif_node"}
    filtered_tags = [t for t in tags if t not in system_tags]
    
    # Build new payload
    new_payload = {
        "text": text,
        "meta": metadata
    }
    new_payload_bytes = json.dumps(new_payload).encode()
    new_nonce, new_ciphertext = encrypt_aes(new_payload_bytes, key)
    
    # Build new entry
    new_entry = {
        "id": old_entry["id"],
        "type": mem_type,
        "created_at": old_entry.get("timestamp", datetime.now(timezone.utc).isoformat()),
        "tags": filtered_tags,
        "payload_nonce": new_nonce.hex(),
        "payload": new_ciphertext.hex(),
    }
    
    # Copy embedding if present
    if "embedding" in old_entry:
        new_entry["embedding"] = old_entry["embedding"]
    
    return new_entry


def migrate_file(source_file: Path, key: bytes, force_type: str = None, verbose: bool = False) -> tuple[list, int]:
    """Migrate entries from a source file. Returns (entries, failed_count)."""
    if not source_file.exists():
        return [], 0
    
    entries = []
    failed = 0
    with open(source_file, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                try:
                    old_entry = json.loads(line)
                    # Skip if missing required fields
                    if "content_nonce" not in old_entry or "content" not in old_entry:
                        failed += 1
                        continue
                    new_entry = transform_entry(old_entry, key, force_type)
                    entries.append(new_entry)
                except Exception as e:
                    failed += 1
                    if verbose:
                        print(f"  ⚠️ Failed: {e}", file=sys.stderr)
                    continue
    
    return entries, failed


def backup_files(files: list[Path], backup_dir: Path):
    """Backup files before migration."""
    backup_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    for f in files:
        if f.exists():
            backup_name = f"{f.stem}_{timestamp}{f.suffix}"
            backup_path = backup_dir / backup_name
            shutil.copy2(f, backup_path)
            print(f"  📦 Backed up: {f.name} -> {backup_name}")


def main():
    parser = argparse.ArgumentParser(description="Migrate memory to unified schema")
    parser.add_argument("agent", help="Agent name (e.g., opus)")
    parser.add_argument("--dry-run", action="store_true", help="Show what would be migrated")
    parser.add_argument("--force", action="store_true", help="Re-migrate even if unified file exists")
    args = parser.parse_args()
    
    # Load agent config
    try:
        paths = get_agent_paths(args.agent)
    except ValueError as e:
        print(f"❌ {e}", file=sys.stderr)
        sys.exit(1)
    
    private_path = paths["private"]
    shared_path = paths["shared"]
    
    print(f"🔄 Memory Migration for {args.agent}")
    print(f"   Private: {private_path}")
    print(f"   Shared: {shared_path}")
    
    # Check if already migrated
    unified_file = private_path / "unified_memories.jsonl"
    if unified_file.exists() and not args.force:
        with open(unified_file, "r") as f:
            first_line = f.readline()
            if first_line:
                header = json.loads(first_line)
                if header.get("version") == FILE_VERSION:
                    print(f"✅ Already migrated (v{FILE_VERSION}). Use --force to re-migrate.")
                    sys.exit(0)
    
    # Load passphrases from .env
    try:
        private_pass, shared_pass = load_passphrases(args.agent)
    except ValueError as e:
        print(f"❌ {e}", file=sys.stderr)
        sys.exit(1)
    
    # Derive keys using fixed salts (same as SemanticMemory.unlock)
    private_key = derive_memory_key(private_pass)
    
    # Shared key
    shared_key = None
    if shared_path and shared_pass:
        shared_key = derive_memory_key(shared_pass)
    
    # Source files
    private_sources = {
        "semantic_memories.jsonl": None,  # infer type
        "journal_memories.jsonl": "sys_journal",
        "shapes.jsonl": "sys_shape",
    }
    
    shared_sources = {
        "semantic_memories.jsonl": "sys_understanding",
    }
    
    # Count source entries
    print("\n📊 Source inventory:")
    total_source = 0
    
    for filename in private_sources:
        f = private_path / filename
        if f.exists():
            count = sum(1 for _ in open(f, "r", encoding="utf-8") if _.strip())
            print(f"   {filename}: {count} entries")
            total_source += count
    
    if shared_key:
        for filename in shared_sources:
            f = shared_path / filename
            if f.exists():
                count = sum(1 for _ in open(f, "r", encoding="utf-8") if _.strip())
                print(f"   shared/{filename}: {count} entries")
                total_source += count
    
    print(f"   Total source: {total_source} entries")
    
    if args.dry_run:
        print("\n🔍 Dry run - no changes made")
        sys.exit(0)
    
    # Backup
    print("\n📦 Creating backups...")
    backup_dir = private_path / "backups" / "pre_unification"
    backup_files(
        [private_path / f for f in private_sources.keys()] + [shared_path / "semantic_memories.jsonl"],
        backup_dir
    )
    
    # Archive dreams.jsonl
    dreams_file = private_path / "dreams.jsonl"
    if dreams_file.exists():
        archive_dir = private_path / "archive"
        archive_dir.mkdir(parents=True, exist_ok=True)
        archive_path = archive_dir / "dreams_legacy.jsonl"
        shutil.copy2(dreams_file, archive_path)
        print(f"  📦 Archived: dreams.jsonl -> archive/dreams_legacy.jsonl")
    
    # Migrate private
    print("\n🔄 Migrating private memories...")
    all_private_entries = []
    total_private_failed = 0
    for filename, force_type in private_sources.items():
        source_file = private_path / filename
        if source_file.exists():
            entries, failed = migrate_file(source_file, private_key, force_type)
            print(f"   {filename}: {len(entries)} migrated, {failed} failed (wrong key)")
            all_private_entries.extend(entries)
            total_private_failed += failed
    
    # Deduplicate by ID (keep newest)
    seen_ids = {}
    for entry in all_private_entries:
        existing = seen_ids.get(entry["id"])
        if existing is None or entry["created_at"] > existing["created_at"]:
            seen_ids[entry["id"]] = entry
    all_private_entries = list(seen_ids.values())
    
    # Write private unified file
    header = {"version": FILE_VERSION, "embedding_model": EMBEDDING_MODEL}
    with open(unified_file, "w", encoding="utf-8") as f:
        f.write(json.dumps(header) + "\n")
        for entry in all_private_entries:
            f.write(json.dumps(entry) + "\n")
    print(f"   ✅ Wrote {len(all_private_entries)} entries to unified_memories.jsonl")
    
    # Migrate shared
    if shared_key:
        print("\n🔄 Migrating shared memories...")
        shared_unified = shared_path / "unified_memories.jsonl"
        all_shared_entries = []
        total_shared_failed = 0
        for filename, force_type in shared_sources.items():
            source_file = shared_path / filename
            if source_file.exists():
                entries, failed = migrate_file(source_file, shared_key, force_type)
                print(f"   {filename}: {len(entries)} migrated, {failed} failed (wrong key)")
                all_shared_entries.extend(entries)
                total_shared_failed += failed
        
        with open(shared_unified, "w", encoding="utf-8") as f:
            f.write(json.dumps(header) + "\n")
            for entry in all_shared_entries:
                f.write(json.dumps(entry) + "\n")
        print(f"   ✅ Wrote {len(all_shared_entries)} entries to shared unified_memories.jsonl")
    else:
        total_shared_failed = 0
        all_shared_entries = []
    
    # Verify
    print("\n✅ Verification:")
    total_migrated = len(all_private_entries) + len(all_shared_entries)
    total_failed = total_private_failed + total_shared_failed
    print(f"   Source entries: {total_source}")
    print(f"   Migrated entries: {total_migrated}")
    print(f"   Failed (wrong key): {total_failed}")
    
    if total_migrated + total_failed >= total_source:
        print("   ✅ All entries accounted for!")
    else:
        diff = total_source - total_migrated - total_failed
        print(f"   ⚠️ Unaccounted: {diff} entries")
    
    print("\n🎉 Migration complete!")
    print("   Old files preserved in backups/pre_unification/")
    print("   Run verbs with new unified store to test")


if __name__ == "__main__":
    main()
