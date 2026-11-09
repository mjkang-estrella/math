"""Frozen-input verification for lane common-basis-audit-supplement-pi-r3.
Usage: python3 -I -B verify_frozen_r3.py before|after
Checks every sha256 in frozen-inputs.json against the bound original file; writes
receipts/frozencheck-<phase>.json. Read-only wrt the bound originals."""
import json, hashlib, pathlib, sys, datetime

LANE = pathlib.Path(__file__).resolve().parents[1]
phase = sys.argv[1]
d = json.load((LANE / 'frozen-inputs.json').open())
bad = []
for p, h in d.items():
    q = pathlib.Path(p)
    if not q.exists():
        bad.append({'path': p, 'issue': 'missing'}); continue
    a = hashlib.sha256(q.read_bytes()).hexdigest()
    if a != h:
        bad.append({'path': p, 'issue': 'mismatch', 'actual': a, 'expected': h})
out = {'phase': phase, 'entries': len(d), 'bad_count': len(bad), 'bad': bad,
       'status': 'ok' if not bad else 'FAIL',
       'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
rc = LANE / 'receipts'; rc.mkdir(parents=True, exist_ok=True)
(rc / f'frozencheck-{phase}.json').write_text(json.dumps(out, indent=1) + '\n')
print(json.dumps({'phase': phase, 'entries': len(d), 'bad_count': len(bad), 'status': out['status']}))
sys.exit(0 if not bad else 1)
