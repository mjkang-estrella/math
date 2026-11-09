#!/usr/bin/env python3
"""Final verifier for lane pi-mathdb-primary-qualified-breadth-r343.
Rehashes every binding's ORIGINAL bytes (every reference carries sha256+size; existence-only
refs are forbidden), rehashes every payload against manifest.json, enforces the exact payload
set (manifest.json and verification-receipt.json excluded), enforces reservation-disjointness
and the 50/2 counts. Exits NONZERO on any failure; writes verification-receipt.json on PASS.
Usage: python3 verify.py [verify]
"""
import json, hashlib, sys, datetime
from pathlib import Path

R = Path(__file__).resolve().parent
LANES = R.parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def fail(msg):
    print("VERIFY FAIL:", msg)
    sys.exit(1)

def main():
    # 1) Bindings: every entry must carry a real sha256 and the original bytes must match.
    bs = json.loads((R/'bindings.json').read_text())
    if not bs.get('references'): fail("no binding references")
    for e in bs['references']:
        if 'sha256' not in e or 'size' not in e:
            fail(f"existence-only binding ref (no hash): {e}")
        p = Path(e['original'])
        if not p.is_file(): fail(f"binding original missing: {e['original']}")
        if sha(p) != e['sha256'] or p.stat().st_size != e['size']:
            fail(f"binding hash/size mismatch: {e['original']}")

    # 2) Payload set + manifest rehash. Manifest covers EVERY payload except itself and the receipt.
    payload = {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()} - {'manifest.json', 'verification-receipt.json'}
    man = json.loads((R/'manifest.json').read_text())
    declared = {e['path'] for e in man['files']}
    if payload != declared:
        fail(f"payload set mismatch: missing={sorted(payload-declared)} extra={sorted(declared-payload)}")
    for e in man['files']:
        p = R/e['path']
        if sha(p) != e['sha256'] or p.stat().st_size != e['size']:
            fail(f"manifest hash/size mismatch: {e['path']}")

    # 3) Reservation-disjointness and counts against the immutable root inputs.
    res = json.loads((LANES/'root-mathdb-core-retirement-r342/reserved-ids.json').read_text())
    ids = [str(i) for i in res['ids']]
    if not (len(ids) == len(set(ids)) == 50): fail("reserved ids not 50 unique")
    cov = json.loads((LANES/'root-mathdb-core-retirement-r342/coverage-delta.json').read_text())
    if set(ids) & set(cov): fail("reserved ids overlap coverage-delta")
    disp = json.loads((R/'dispositions.json').read_text())['dispositions']
    if set(disp) != set(ids): fail(f"dispositions ids != reserved ids (missing={sorted(set(ids)-set(disp))} extra={sorted(set(disp)-set(ids))})")
    props = json.loads((R/'proposals.json').read_text())['proposals']
    if len(props) > 3: fail("more than 3 proposals")
    for pr in props:
        if str(pr['mathdb_id']) not in ids: fail(f"proposal id {pr['mathdb_id']} not reserved")

    # 4) Corpus chunks bound here must still match the inventory manifest (defense in depth).
    inv = json.loads((LANES/'pi-mathdb-full-corpus-inventory-r301/manifest.json').read_text())
    invmap = {e['path']: e for e in inv['files']}
    for e in bs['references']:
        rel = str(Path(e['original']))
        if 'corpus/mathdb-normalized-chunk-' in rel:
            key = 'corpus/' + Path(e['original']).name
            if sha(Path(e['original'])) != invmap[key]['sha256']:
                fail(f"corpus chunk no longer matches inventory manifest: {key}")

    receipt = {
        "status": "PASS",
        "at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "binding_refs": len(bs['references']),
        "payloads": len(payload),
        "dispositions": len(disp),
        "proposals": len(props),
        "reservation_disjoint": True
    }
    (R/'verification-receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print("VERIFY PASS:", json.dumps(receipt, sort_keys=True))

if __name__ == '__main__':
    main()
