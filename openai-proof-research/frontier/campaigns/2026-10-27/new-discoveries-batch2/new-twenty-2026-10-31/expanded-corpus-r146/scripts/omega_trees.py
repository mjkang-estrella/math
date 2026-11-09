# Fetch complete D5 and Problems trees of the-omega-institute/trureturing at the HEAD tree recorded in outputs/registry-heads.json
import json, urllib.request, hashlib, datetime, pathlib, re
D = pathlib.Path(__file__).resolve().parents[1]
heads = json.loads((D / 'outputs/registry-heads.json').read_text())
tree = heads['the-omega-institute/trureturing']['tree']
def get(u):
    req = urllib.request.Request(u, headers={'User-Agent': 'research-lane-fetch/1.0', 'Accept': 'application/vnd.github+json'})
    with urllib.request.urlopen(req, timeout=40) as r: return r.read(), r.status
rec = {}
root, st = get(f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{tree}')
(D / 'sources/omega-root.json').write_bytes(root)
rec['root'] = dict(status=st, sha256=hashlib.sha256(root).hexdigest(), tree=tree)
for name in ['D5', 'Problems']:
    sub = [e for e in json.loads(root)['tree'] if e['path'] == name]
    if not sub: rec[name] = 'absent at root'; continue
    b, st = get(f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sub[0]["sha"]}?recursive=1')
    (D / f'sources/omega-{name}.json').write_bytes(b)
    j = json.loads(b)
    rec[name] = dict(status=st, sha=sub[0]['sha'], sha256=hashlib.sha256(b).hexdigest(), entries=len(j['tree']), truncated=j['truncated'])
rec['utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
pats = ['riordan', 'catalan-graph', 'catalangraph', 'set-sequential', 'setsequential', 'balister', 'dendrimer', 'dehmer', 'latin-array', 'latinarray', 'akbari', 'transversal', 'fuglede', 'spectral-set', 'incidence', 'hypercube', 'hypertree', 'grothendieck', 'ribbon', 'fair-represent', 'fairrepresent', 'subgroup', 'toth', 'chromatic-polynomial', 'chromaticpolynomial', 'brown-erey', 'tomescu', 'homothet', 'secant', 'arboricity', 'irregular', 'locally-irregular', 'multiple-list', 'choosab', 'tree-decomposition', 'contractive', 'milicevic', 'blue-path', 'monochromatic-path', 'guggiari']
hits = {}
for name in ['D5', 'Problems']:
    f = D / f'sources/omega-{name}.json'
    if not f.exists(): continue
    for e in json.loads(f.read_text())['tree']:
        p = e['path'].lower()
        for q in pats:
            if q in p: hits.setdefault(q, []).append(name + '/' + e['path'])
rec['path_screen_hits'] = {k: v[:20] for k, v in hits.items()}
rec['path_screen_patterns'] = pats
(D / 'outputs/omega-tree-screen.json').write_text(json.dumps(rec, indent=2) + '\n')
print(json.dumps({k: (v if k != 'path_screen_hits' else {q: len(x) for q, x in v.items()}) for k, v in rec.items() if k != 'path_screen_patterns'}, indent=1))
