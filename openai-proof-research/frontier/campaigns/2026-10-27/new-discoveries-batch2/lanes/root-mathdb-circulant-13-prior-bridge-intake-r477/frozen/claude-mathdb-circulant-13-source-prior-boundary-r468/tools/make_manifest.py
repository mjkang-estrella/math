"""Write manifest.json: exact set of lane files (sha256,size) excluding ONLY manifest.json
and verification-receipt.json. usage: make_manifest.py LANE_DIR"""
import hashlib, json, os, sys
lane = sys.argv[1]
EXC = {'manifest.json', 'verification-receipt.json'}
files = []
for r, _, fs in os.walk(lane):
    for f in fs:
        rel = os.path.relpath(os.path.join(r, f), lane)
        if rel in EXC:
            continue
        b = open(os.path.join(r, f), 'rb').read()
        files.append({'path': rel, 'sha256': hashlib.sha256(b).hexdigest(), 'size': len(b)})
files.sort(key=lambda e: e['path'])
json.dump({'excluded': sorted(EXC), 'files': files}, open(os.path.join(lane, 'manifest.json'), 'w'), indent=1)
print(len(files))
