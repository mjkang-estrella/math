"""Separate verification: recompute every manifest hash, confirm no unlisted files
(other than manifest.json and verification-receipt.json), re-check scientific freeze."""
import os, json, hashlib, datetime
h = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
m = json.load(open('manifest.json'))
bad = [p for p, r in m['files'].items() if not os.path.exists(p) or h(p) != r['sha256']]
present = set()
for root, _, fs in os.walk('.'):
    for f in fs:
        present.add(os.path.relpath(os.path.join(root, f), '.'))
extra = sorted(present - set(m['files']) - {'manifest.json', 'verification-receipt.json'})
fb = json.load(open('receipts/freeze-before.json'))
sci = {n: h(os.path.join('..', '..', r['original'])) == r['sha256_original'] for n, r in fb['scientific'].items()}
rec = {'verified_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'manifest_sha256': h('manifest.json'),
       'files_checked': len(m['files']), 'mismatches': bad, 'unlisted_files': extra, 'scientific_originals_unchanged': sci,
       'pass': not bad and not extra and all(sci.values())}
json.dump(rec, open('verification-receipt.json', 'w'), indent=1)
print(json.dumps(rec))
