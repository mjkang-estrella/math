import hashlib, json, os, sys, datetime
# Supplemental hash-only references (no copying) for cached bodies read from the predecessor lane.
# Usage: bind_supplement.py bind | verify
L = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/claude-richardson-prior-substantive-r2'
S = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-hankel-breadth-depth-r1/sources/'
FILES = {'berg.pdf': '2813148b9e7d1c56a3971ef8a529a3921d0b27d80afa7f0b6a796740fc180b8c',
         'berg.txt': None,
         'fq.pdf': '09eebfb07b263e5dd20e935f114888e31433266f572966dbf0ede2afaf233d4e',
         'fq.txt': None}
OUT = L + '/reference-bindings-supplement.json'
h = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
if sys.argv[1] == 'bind':
    assert not os.path.exists(OUT)
    rec = {'bound_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'note': 'Bound AFTER native reads of berg.txt/fq.txt in this lane (custody deviation, see FAILURES.md). PDFs compared with inherited receipt hashes.',
           'files': []}
    for f, inherited in FILES.items():
        d = h(S + f)
        rec['files'].append({'path': S + f, 'sha256': d, 'inherited_receipt_sha256': inherited,
                             'matches_inherited': (d == inherited) if inherited else None})
    json.dump(rec, open(OUT, 'w'), indent=1); print(json.dumps(rec, indent=1))
else:
    rec = json.load(open(OUT))
    ok = all(h(e['path']) == e['sha256'] for e in rec['files'])
    print(json.dumps({'supplement_ok': ok})); sys.exit(0 if ok else 1)
