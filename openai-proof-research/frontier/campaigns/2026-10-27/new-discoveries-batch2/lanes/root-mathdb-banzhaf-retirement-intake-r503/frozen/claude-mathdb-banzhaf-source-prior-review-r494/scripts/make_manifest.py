import hashlib, json, os, sys
lane = sys.argv[1]; ex = ['manifest.json', 'verification-receipt.txt']; files = []
for r, ds, fs in os.walk(lane):
    for f in fs:
        p = os.path.relpath(os.path.join(r, f), lane)
        if p in ex: continue
        d = open(os.path.join(lane, p), 'rb').read()
        files.append({'path': p, 'sha256': hashlib.sha256(d).hexdigest(), 'size': len(d)})
files.sort(key=lambda e: e['path'])
json.dump({'lane': os.path.basename(lane), 'excluded_exact_paths': ex, 'files': files}, open(os.path.join(lane, 'manifest.json'), 'w'), indent=1)
print(len(files))
