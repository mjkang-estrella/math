"""usage: manifest.py LANE_DIR build|verify
build: write finalmanifest.json over every lane file except finalmanifest.json and verification-receipt.json.
verify: re-hash and write verification-receipt.json."""
import sys, os, json, hashlib, datetime
L, mode = sys.argv[1], sys.argv[2]
EXCL = {'finalmanifest.json', 'verification-receipt.json'}
def files():
    for root, _, fs in os.walk(L):
        for f in fs:
            rel = os.path.relpath(os.path.join(root, f), L)
            if rel not in EXCL: yield rel
h = lambda p: hashlib.sha256(open(os.path.join(L, p), 'rb').read()).hexdigest()
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
if mode == 'build':
    M = {'utc': now, 'excluded_explicitly': sorted(EXCL), 'files': {p: h(p) for p in sorted(files())}}
    json.dump(M, open(os.path.join(L, 'finalmanifest.json'), 'w'), indent=1); print('built', len(M['files']))
else:
    M = json.load(open(os.path.join(L, 'finalmanifest.json')))
    cur = set(files()); listed = set(M['files'])
    bad = sorted(p for p in listed & cur if h(p) != M['files'][p])
    R = {'utc': now, 'manifest_sha256': h('finalmanifest.json'), 'files_listed': len(listed), 'missing': sorted(listed - cur),
         'unlisted': sorted(cur - listed), 'mismatched': bad, 'excluded_explicitly': sorted(EXCL),
         'ok': not bad and listed == cur}
    json.dump(R, open(os.path.join(L, 'verification-receipt.json'), 'w'), indent=1); print(json.dumps(R))
