"""Post-write freeze comparison and manifest. Run from the lane directory.
Manifest excludes itself and verification-receipt.json."""
import os, json, hashlib, datetime
h = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
fb = json.load(open('receipts/freeze-before.json'))
after = {'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'items': {}}
lane_prefix = 'lanes/claude-tang-tang-source-classical-boundary-r2/'
for grp in ('scientific', 'administrative_snapshot'):
    for n, r in fb[grp].items():
        orig = os.path.join('..', '..', r['original'])
        copy = r['copy'][len(lane_prefix):]
        after['items'][n] = {'group': grp, 'original_now': h(orig), 'copy_now': h(copy), 'before': r['sha256_original'],
                             'original_unchanged': h(orig) == r['sha256_original'], 'copy_unchanged': h(copy) == r['sha256_copy']}
reused = {'../sol-tang-tang-stable-approximation-preliminary-review-r1/frozen/1908.10024v1.pdf': '707c90da8b2f3f14765854b023f6133b685be271de7bbdae002fbb71c56d44be',
          '../sol-tang-tang-stable-approximation-preliminary-review-r1/frozen/1908.10024v1.txt': 'd0d307bb7b4fd60b99aa241a5c38a22f5437667b87fe77e3f16b7a21c6523454',
          '../sol-tang-tang-stable-approximation-preliminary-review-r1/frozen/1607.03036v1.pdf': 'b32af89a58e9316c4e48c9966d03f13eaee7ddbc987716a4db43daa5f1a479ba',
          '../sol-tang-tang-stable-approximation-preliminary-review-r1/frozen/1607.03036v1.txt': '50cf07a2bcc6e05a3401b597dd570efe1ccaa428f399c9ff76ef5d983325df3b'}
after['reused_immutable_references'] = {p: {'expected': v, 'now': h(p), 'ok': h(p) == v} for p, v in reused.items()}
json.dump(after, open('receipts/freeze-after.json', 'w'), indent=1)
assert all(v['original_unchanged'] and v['copy_unchanged'] for v in after['items'].values() if v['group'] == 'scientific')
assert all(v['ok'] for v in after['reused_immutable_references'].values())
files = {}
for root, _, fs in os.walk('.'):
    for f in fs:
        p = os.path.relpath(os.path.join(root, f), '.')
        if p in ('manifest.json', 'verification-receipt.json'):
            continue
        files[p] = {'sha256': h(p), 'bytes': os.path.getsize(p)}
json.dump({'created_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'excludes': ['manifest.json', 'verification-receipt.json'], 'files': dict(sorted(files.items()))},
          open('manifest.json', 'w'), indent=1)
print(len(files), 'files; admin unchanged:', {k: v['original_unchanged'] for k, v in after['items'].items() if v['group'] != 'scientific'})
