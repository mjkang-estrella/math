"""Write manifest.json covering every lane file except manifest.json and final-receipt.json.
Usage (lane dir): python3 -I -B scripts/make_manifest.py"""
import hashlib, json, os
EXCLUDED = ['final-receipt.json', 'manifest.json']
files = []
for d, ds, fs in os.walk('.'):
    ds.sort()
    for f in sorted(fs):
        rel = os.path.relpath(os.path.join(d, f), '.')
        if rel in EXCLUDED: continue
        assert not os.path.islink(rel), rel
        b = open(rel, 'rb').read()
        files.append({'path': rel, 'size': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
files.sort(key=lambda e: e['path'])
json.dump({'excluded_exact_paths': EXCLUDED, 'files': files}, open('manifest.json', 'w'), indent=1)
print(len(files))
