import hashlib, json, os, shutil, sys, datetime
# Usage: bind.py bind | bind.py verify
B = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'
L = B + '/lanes/claude-richardson-prior-substantive-r2'
SCI = [
    'lanes/sol-hankel-full-prime-power-r2/PROOF.md',
    'lanes/sol-hankel-full-prime-power-r2/discovery.md',
    'lanes/sol-richardson-integrality-preliminary-review-r1/review.md',
    'lanes/sol-richardson-integrality-preliminary-review-r1/provenance.json',
]
# immutable qualified history references: hash only, no recursive copying
REF = [
    'lanes/sol-hankel-full-prime-power-r2/scout.md',
    'lanes/sol-hankel-full-prime-power-r2/http.jsonl',
    'lanes/sol-hankel-full-prime-power-r2/manifest.json',
    'lanes/sol-richardson-integrality-preliminary-review-r1/http.jsonl',
    'lanes/sol-richardson-integrality-preliminary-review-r1/manifest.json',
    'lanes/sol-richardson-integrality-preliminary-review-r1/independent_check.py',
    'lanes/root-richardson-prior-gate-r1/DISPOSITION.md',
    'lanes/root-hankel-prime-power-route-r1/route.txt',
    'lanes/sol-hankel-breadth-depth-r1/scout.md',
    'lanes/sol-hankel-breadth-depth-r1/discovery.md',
]
ADMIN = ['NEXT.md', 'ledger.json', 'prior-campaign-context.json', 'AGENTS.md']

def h(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

if sys.argv[1] == 'bind':
    assert not os.path.exists(L + '/input-bindings.json')
    out = {'bound_at_utc': now(), 'scientific': [], 'references': [], 'administrative_snapshots': []}
    for rel in SCI:
        src = B + '/' + rel
        dst = L + '/inputs/' + rel.replace('lanes/', '').replace('/', '__')
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        before = h(src); shutil.copyfile(src, dst); after = h(src)
        assert before == after == h(dst)
        out['scientific'].append({'original': src, 'copy': dst, 'sha256': before, 'bytes': os.path.getsize(src)})
    for rel in REF:
        src = B + '/' + rel
        out['references'].append({'original': src, 'sha256': h(src), 'bytes': os.path.getsize(src)})
    for rel in ADMIN:
        src = B + '/' + rel
        dst = L + '/administrative/' + rel
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(src, dst)
        out['administrative_snapshots'].append({'live_original_not_bound': src, 'snapshot': dst, 'snapshot_sha256': h(dst),
                                                'note': 'administrative snapshot only; live mutable original is not a scientific input'})
    json.dump(out, open(L + '/input-bindings.json', 'w'), indent=1)
    print(json.dumps({'bound': len(SCI), 'refs': len(REF), 'admin': len(ADMIN)}))
else:
    d = json.load(open(L + '/input-bindings.json'))
    res = {'verified_at_utc': now(), 'scientific': [], 'references': [], 'admin_snapshots': []}
    for e in d['scientific']:
        res['scientific'].append({'path': e['original'], 'original_ok': h(e['original']) == e['sha256'], 'copy_ok': h(e['copy']) == e['sha256']})
    for e in d['references']:
        res['references'].append({'path': e['original'], 'ok': h(e['original']) == e['sha256']})
    for e in d['administrative_snapshots']:
        res['admin_snapshots'].append({'path': e['snapshot'], 'ok': h(e['snapshot']) == e['snapshot_sha256']})
    res['all_ok'] = all(x.get('original_ok', True) and x.get('copy_ok', True) and x.get('ok', True)
                        for k in ('scientific', 'references', 'admin_snapshots') for x in res[k])
    print(json.dumps(res, indent=1))
    sys.exit(0 if res['all_ok'] else 1)
