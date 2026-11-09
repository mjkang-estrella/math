import hashlib, json, os, datetime
L = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/claude-richardson-prior-substantive-r2'
EXCLUDE = {'manifest.json', 'verification-receipt.json'}
files = []
for root, _, names in os.walk(L):
    for nm in sorted(names):
        rel = os.path.relpath(os.path.join(root, nm), L)
        if rel in EXCLUDE:
            continue
        p = os.path.join(L, rel)
        files.append({'path': rel, 'sha256': hashlib.sha256(open(p, 'rb').read()).hexdigest(), 'bytes': os.path.getsize(p)})
files.sort(key=lambda e: e['path'])
json.dump({'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'explicitly_excluded': sorted(EXCLUDE),
           'file_count': len(files), 'files': files}, open(L + '/manifest.json', 'w'), indent=1)
print('manifest files', len(files))
