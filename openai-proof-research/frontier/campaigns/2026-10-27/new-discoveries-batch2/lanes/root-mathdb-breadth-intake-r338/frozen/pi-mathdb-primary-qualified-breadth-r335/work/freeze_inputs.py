#!/usr/bin/env python3
"""Freeze scientific inputs for r335 BEFORE reading scientific content.

Binds (sha256+size, immutable in-place references, no corpus copy):
  - r334 reservation + queue + coverage-status
  - r332 frozen coverage-delta (233 IDs)
  - r301 corpus inventory manifest + all 20 normalized chunks
  - r304 accepted-exclusions + historical-dispositions (bound now, read later)
  - r326 frozen review-queue-top.jsonl (ranked metadata source)
Also validates the r334 root manifest logic read-only (does NOT write to r334).
"""
from pathlib import Path
import hashlib, json, sys, datetime

BASE = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
L = BASE / 'lanes'
LANE = L / 'pi-mathdb-primary-qualified-breadth-r335'
R334 = L / 'root-mathdb-stack-intake-r334'
R332F = R334 / 'frozen/root-mathdb-breadth-intake-r332/coverage-delta.json'
R326Q = R334 / 'frozen/root-mathdb-breadth-intake-r326/frozen/pi-mathdb-full-corpus-inventory-r301/tags/review-queue-top.jsonl'
R301 = L / 'pi-mathdb-full-corpus-inventory-r301'
R304 = L / 'root-mathdb-accepted-exclusions-r304'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def bind(original):
    p = Path(original)
    return {'original': str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}

bindings = []
for p in [
    R334 / 'reserved-ids.json', R334 / 'queue.json', R334 / 'coverage-status.json',
    R332F, R326Q, R301 / 'manifest.json',
    *[R301 / f'corpus/mathdb-normalized-chunk-{i:04d}.jsonl' for i in range(1, 21)],
    R304 / 'accepted-exclusions.json', R304 / 'historical-dispositions.json',
]:
    bindings.append(bind(p))

out = {'lane': 'pi-mathdb-primary-qualified-breadth-r335',
       'frozen_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'note': 'immutable in-place references; no corpus copy; scientific content not yet read',
       'bindings': bindings}
(LANE / 'bindings.json').write_text(json.dumps(out, indent=2) + '\n')

# --- Validate r334 root manifest read-only (replicates r334 verify.py assertions) ---
errs = []
def chk(cond, msg):
    if not cond: errs.append(msg)

reserved = json.loads((R334 / 'reserved-ids.json').read_text())
chk(reserved['lane'] == 'pi-mathdb-primary-qualified-breadth-r335', 'r334 reserved lane mismatch')
chk(reserved['status'] == 'reserved_not_reviewed', 'r334 reserved status')
chk(len(reserved['ids']) == 50 and len(set(reserved['ids'])) == 50, 'r334 reserved ids not 50 unique')

coverage = json.loads(R332F.read_text())
chk(len(coverage) == 233, f'coverage len {len(coverage)} != 233')
chk('347483' in coverage, '347483 not in coverage')
chk(not (set(map(str, reserved['ids'])) & set(coverage)), 'reserved overlap with 233 coverage')

queue = [json.loads(s) for s in R326Q.read_text().splitlines()]
selected, seen = [], set(coverage)
for row in queue:
    n = str(row['mathdb_id'])
    if n in seen or row['statement_completeness'] != 'full' or row['status'] != 'open':
        continue
    selected.append(row); seen.add(n)
    if len(selected) == 50: break
chk(len(selected) == 50, 're-derived selection != 50')
chk([r['mathdb_id'] for r in selected] == reserved['ids'], 're-derived selection != reserved ids')

own = json.loads((R334 / 'manifest.json').read_text())['files']
def payload(root):
    return {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()} - {'manifest.json', 'verification-receipt.json'}
chk(payload(R334) == {e['path'] for e in own}, 'r334 payload set mismatch')
for e in own:
    p = R334 / e['path']
    size_key = 'bytes' if 'bytes' in e else 'size'
    chk(sha(p) == e['sha256'] and p.stat().st_size == e[size_key], f'r334 payload hash {e["path"]}')

# --- Verify corpus chunks against r301 inventory manifest BEFORE content ---
inv = json.loads((R301 / 'manifest.json').read_text())
by_path = {e['path']: e for e in inv['files']}
for i in range(1, 21):
    rel = f'corpus/mathdb-normalized-chunk-{i:04d}.jsonl'
    e = by_path.get(rel)
    chk(e is not None, f'{rel} missing from inventory manifest')
    if e:
        p = R301 / rel
        chk(sha(p) == e['sha256'] and p.stat().st_size == e['bytes'], f'chunk hash mismatch {rel}')
        # also match against our own binding
b = {(Path(x['original']).name): x for x in bindings}
for e in inv['files']:
    if e['path'].startswith('corpus/'):
        chk(e['sha256'] == b.get(Path(e['path']).name, {}).get('sha256'), f'binding vs manifest mismatch {e["path"]}')

result = {'status': 'PASS' if not errs else 'FAIL', 'errors': errs,
          'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'bindings': len(bindings), 'coverage_ids': len(coverage),
          'reserved_ids': len(reserved['ids']), 'chunks_verified': 20}
(LANE / 'work/freeze-result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
sys.exit(0 if not errs else 1)
