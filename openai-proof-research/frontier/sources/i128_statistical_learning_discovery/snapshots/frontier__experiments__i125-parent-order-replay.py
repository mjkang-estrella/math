"""Parent ordering-only replay; original failed seal and verifier stay unchanged.

Sort only the in-memory inventory rows. Reuse every original membership,
hash, size, provenance and diagnostic check. No write or reseal operation.
"""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parents[2]
VERIFIER = ROOT / 'frontier/experiments/i125_dini_singular_packing/verify.py'
SEAL = ROOT / 'frontier/sources/i125_dini_singular_packing/seal.json'
assert hashlib.sha256(VERIFIER.read_bytes()).hexdigest() == '01bcbb659a7eef2c5fce48cb8034802a9925701fec837a2ddb47d9a57f5cfc68'
assert hashlib.sha256(SEAL.read_bytes()).hexdigest() == '8fdd857eeccb0d61279b428c5148915fee4d858fbc63dbc4061b1e2ee9b87f2f'
original = runpy.run_path(str(VERIFIER), run_name='i125_parent_bound_original')
sys.addaudithook(original['readonly_hook'])
seal = original['obj'](original['SEAL'])
paths = [row['path'] for row in seal['files']]
assert len(paths) == len(set(paths)) == 42
assert paths != sorted(paths), 'Original ordering failure must remain reproducible'
ordered = dict(seal, files=sorted(seal['files'], key=lambda row: row['path']))
inventory = original['inventory'](ordered)
validation = original['core']()
print(json.dumps({
    'status': 'PASS',
    'original_verifier_status': 'FAIL: ValueError: canonical inventory',
    'correction': 'Only inventory-row order normalized in memory; no sealed byte changed',
    'offline': True,
    'read_only': True,
    'corpus_replays': 1,
    'inventory': inventory,
    'validation': validation,
    'certifies': 'artifact identities, exact memberships and finite diagnostics only',
}, indent=2, sort_keys=True))
