#!/usr/bin/env python3
"""Verify all frozen-input hashes; write evidence/frozen-<phase>.json. Read-only on inputs."""
import json, hashlib, sys, os, datetime
LANE = os.path.dirname(os.path.abspath(__file__))
phase = sys.argv[1] if len(sys.argv) > 1 else 'after'
manifest = json.load(open(os.path.join(LANE, 'frozen-inputs.json')))
missing, mismatch, ok = [], [], 0
for path, want in sorted(manifest.items()):
    if not os.path.exists(path):
        missing.append(path); continue
    h = hashlib.sha256(open(path, 'rb').read()).hexdigest()
    if h == want: ok += 1
    else: mismatch.append({'path': path, 'expected': want, 'actual': h})
out = {
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'phase': phase, 'total': len(manifest), 'ok': ok,
    'missing': missing, 'mismatch': mismatch,
    'all_ok': not missing and not mismatch,
}
os.makedirs(os.path.join(LANE, 'evidence'), exist_ok=True)
with open(os.path.join(LANE, 'evidence', 'frozen-%s.json' % phase), 'w') as f:
    json.dump(out, f, indent=1)
print(json.dumps({k: out[k] for k in ('phase', 'total', 'ok', 'all_ok')}))
sys.exit(0 if out['all_ok'] else 1)
