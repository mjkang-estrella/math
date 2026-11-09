import hashlib, json, os, sys, datetime
# Hash-only reference to the r216 Cigler-Tyson body (root pointer received mid-task); no copying.
# Usage: bind_r216.py bind | verify
L = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/claude-richardson-prior-substantive-r2'
R = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-wide-structural-analytic-scout-r216/'
FILES = ['sources/1807.08330v2.pdf', 'SCOUTING.md', 'discovery.md', 'http.jsonl']
OUT = L + '/reference-bindings-r216.json'
h = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
if sys.argv[1] == 'bind':
    assert not os.path.exists(OUT)
    rec = {'bound_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'note': 'Bound before reading; pointer supplied by root after completed r216 scout.',
           'files': [{'path': R + f, 'sha256': h(R + f), 'bytes': os.path.getsize(R + f)} for f in FILES]}
    json.dump(rec, open(OUT, 'w'), indent=1); print(json.dumps(rec, indent=1))
else:
    rec = json.load(open(OUT))
    ok = all(h(e['path']) == e['sha256'] for e in rec['files'])
    print(json.dumps({'r216_refs_ok': ok})); sys.exit(0 if ok else 1)
