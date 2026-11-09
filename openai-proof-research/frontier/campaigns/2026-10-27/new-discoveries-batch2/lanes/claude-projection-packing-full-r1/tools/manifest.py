"""Build manifest.json: sha256/bytes of every lane file, EXPLICITLY excluding manifest.json itself
and verification-receipt.json (and the empty scratch dir tmp/)."""
import hashlib, json, os
L = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
EXCLUDED = ['manifest.json', 'verification-receipt.json']
files = []
for root, dirs, names in os.walk(L):
    dirs[:] = sorted(d for d in dirs if d not in ('tmp', '__pycache__'))
    for nm in sorted(names):
        rel = os.path.relpath(os.path.join(root, nm), L)
        if rel in EXCLUDED: continue
        b = open(os.path.join(L, rel), 'rb').read()
        files.append({'path': rel, 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
json.dump({'lane': 'claude-projection-packing-full-r1', 'excluded_explicitly': EXCLUDED,
           'excluded_dirs': ['tmp/ (lp scratch, must be empty)'], 'files': files},
          open(os.path.join(L, 'manifest.json'), 'w'), indent=1)
print(json.dumps({'manifest_files': len(files)}))
