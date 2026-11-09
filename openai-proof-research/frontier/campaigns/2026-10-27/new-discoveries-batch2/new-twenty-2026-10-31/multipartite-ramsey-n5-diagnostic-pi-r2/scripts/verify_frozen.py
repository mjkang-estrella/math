#!/usr/bin/env python3
"""Verify every path:sha256 entry of frozen-inputs.json. Writes before/after record."""
import json, hashlib, sys, os, datetime

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()

def main(out_name, note):
    frozen = json.load(open(os.path.join(BASE, 'frozen-inputs.json')))
    ok, bad, missing = 0, [], []
    for path, want in frozen.items():
        if not os.path.exists(path):
            missing.append(path)
            continue
        got = sha(path)
        if got == want:
            ok += 1
        else:
            bad.append({'path': path, 'want': want, 'got': got})
    rec = {
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'phase': note,
        'entries': len(frozen),
        'verified': ok,
        'mismatched': bad,
        'missing': missing,
        'all_ok': not bad and not missing,
    }
    with open(os.path.join(BASE, out_name), 'w') as f:
        json.dump(rec, f, indent=1, sort_keys=True)
    print(json.dumps({k: rec[k] for k in ('phase', 'entries', 'verified', 'all_ok')}))
    return 0 if rec['all_ok'] else 1

if __name__ == '__main__':
    sys.exit(main(sys.argv[1], sys.argv[2]))
