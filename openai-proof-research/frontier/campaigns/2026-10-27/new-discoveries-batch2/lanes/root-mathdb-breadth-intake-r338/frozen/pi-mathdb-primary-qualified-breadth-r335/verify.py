#!/usr/bin/env python3
"""SEPARATE final verifier for lane pi-mathdb-primary-qualified-breadth-r335.

Checks, independently of the producing scripts:
  1. every binding original file's actual sha256+size matches bindings.json;
  2. all 20 corpus chunks hash-match the r301 inventory manifest;
  3. the 50 reserved records re-extracted from the hash-verified chunks are
     byte-identical (canonical JSON) to the retained copy
     sources/reserved-records.jsonl, which itself matches its recorded sha256;
  4. the exact lane payload set equals manifest.json's file list, and every
     payload file's sha256+size matches the manifest;
  5. structural checks: 50 unique reserved ids, 50 dispositions, <=3 proposals,
     all proposal ids inside the reserved set, dispositions disjoint from the
     233-ID coverage and from r304 exclusion records.
Exits NONZERO on any failure. Writes verification-receipt.json in both cases.
"""
from pathlib import Path
import hashlib, json, sys, datetime

BASE = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
LANE = BASE / 'lanes/pi-mathdb-primary-qualified-breadth-r335'
R301 = BASE / 'lanes/pi-mathdb-full-corpus-inventory-r301'
R334 = BASE / 'lanes/root-mathdb-stack-intake-r334'
R304 = BASE / 'lanes/root-mathdb-accepted-exclusions-r304'
R332F = R334 / 'frozen/root-mathdb-breadth-intake-r332/coverage-delta.json'

errors = []
def chk(cond, msg):
    if not cond:
        errors.append(msg)

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

# --- 1. bindings: originals ---
B = json.loads((LANE / 'bindings.json').read_text())
for row in B['bindings']:
    p = Path(row['original'])
    chk(sha(p) == row['sha256'], f"binding original hash mismatch: {p}")
    chk(p.stat().st_size == row['bytes'], f"binding original size mismatch: {p}")

# --- 2. corpus chunks vs inventory manifest ---
inv = json.loads((R301 / 'manifest.json').read_text())
by_path = {e['path']: e for e in inv['files']}
for i in range(1, 21):
    rel = f'corpus/mathdb-normalized-chunk-{i:04d}.jsonl'
    e = by_path.get(rel)
    chk(e is not None, f'{rel} absent from inventory manifest')
    if e:
        p = R301 / rel
        chk(sha(p) == e['sha256'] and p.stat().st_size == e['bytes'], f'chunk hash mismatch: {rel}')

# --- 3. retained copy vs fresh re-extraction from chunks ---
want = set(json.loads((R334 / 'reserved-ids.json').read_text())['ids'])
chk(len(want) == 50, 'reserved ids != 50')
found = {}
for i in range(1, 21):
    p = R301 / f'corpus/mathdb-normalized-chunk-{i:04d}.jsonl'
    for line in p.open():
        if not line.strip():
            continue
        r = json.loads(line)
        if r.get('mathdb_id') in want:
            found[r['mathdb_id']] = r
chk(set(found) == want, 're-extraction id set mismatch')

copy_lines = (LANE / 'sources/reserved-records.jsonl').read_text().splitlines()
chk(len(copy_lines) == 50, 'retained copy line count != 50')
recs_copy = {}
for line in copy_lines:
    o = json.loads(line)
    recs_copy[o['mathdb_id']] = o['record']
chk(set(recs_copy) == want, 'retained copy id set mismatch')
for i in want:
    chk(json.dumps(recs_copy[i], sort_keys=True) == json.dumps(found[i], sort_keys=True),
        f'retained record differs from corpus record: {i}')
rec_sha = sha(LANE / 'sources/reserved-records.jsonl')
chk(rec_sha == 'a2bb73e8115edd2c6aee0c237823e2fb392676ae21feb1dce519b74a8f79af16',
    'retained reserved-records.jsonl sha mismatch')

# --- 4. manifest payload set + hashes ---
own = json.loads((LANE / 'manifest.json').read_text())['files']
def payload(root):
    return {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()} - {'manifest.json', 'verification-receipt.json'}
chk(payload(LANE) == {e['path'] for e in own}, 'lane payload set != manifest file set')
for e in own:
    p = LANE / e['path']
    chk(p.is_file(), f'manifest file missing: {e["path"]}')
    if p.is_file():
        chk(sha(p) == e['sha256'], f'manifest sha mismatch: {e["path"]}')
        chk(p.stat().st_size == e['size'], f'manifest size mismatch: {e["path"]}')

# --- 5. structural checks ---
disp = json.loads((LANE / 'dispositions.json').read_text())['dispositions']
chk(len(disp) == 50 and {d['mathdb_id'] for d in disp} == want, 'dispositions != 50 reserved ids')
props = json.loads((LANE / 'proposals.json').read_text())['proposals']
chk(len(props) <= 3, 'more than 3 proposals')
chk(all(p['mathdb_id'] in want for p in props), 'proposal id outside reserved set')
coverage = json.loads(R332F.read_text())
chk(not (set(map(str, want)) & set(coverage)), 'reserved overlap with 233-ID coverage')
ae = json.loads((R304 / 'accepted-exclusions.json').read_text())
hd = json.loads((R304 / 'historical-dispositions.json').read_text())
def collect_ids(o, s):
    if isinstance(o, dict):
        for k, v in o.items():
            if k in ('mathdb_id', 'id') and isinstance(v, int):
                s.add(v)
            else:
                collect_ids(v, s)
    elif isinstance(o, list):
        for v in o:
            collect_ids(v, s)
ae_ids, hd_ids = set(), set()
collect_ids(ae, ae_ids); collect_ids(hd, hd_ids)
chk(not (want & ae_ids), 'reserved id in r304 accepted-exclusions')
chk(not (want & hd_ids), 'reserved id in r304 historical-dispositions')

receipt = {'status': 'PASS' if not errors else 'FAIL',
           'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'bindings_checked': len(B['bindings']),
           'chunks_checked': 20,
           'reserved_records_verified': len(found),
           'dispositions': len(disp),
           'proposals': len(props),
           'payload_files': len(own),
           'errors': errors}
(LANE / 'verification-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
sys.exit(0 if not errors else 1)
