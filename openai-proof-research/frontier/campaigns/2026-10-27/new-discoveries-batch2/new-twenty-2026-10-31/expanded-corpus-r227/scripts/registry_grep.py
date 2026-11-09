"""Path screen of registry trees (Lean Pool, Omega) and the cached OpenAI/math listing for reserved
IDs, arXiv IDs, author names and keywords. Usage: registry_grep.py LANE"""
import sys, json, pathlib, re
D = pathlib.Path(sys.argv[1]).resolve()
res = json.loads((D / 'reservation.json').read_text())
ids = [str(i) for i in res['ids']]
arx = sorted({r['source_url'].rsplit('/', 1)[1] for r in res['rows']})
kw = ['Mkrtchyan', 'nonconflict', 'non_conflict', 'NonConflict', 'Oberwolfach', 'spouse', 'Ballantine', 'pre2', 'pre_2',
      'Castelnuovo', 'Hibi', 'isolation', 'Frankl', 'UnionClosed', 'union_closed', 'Lasso', 'Thurston', 'skew', 'Klimosova',
      'RamseyFull', 'Gallai', 'additive_complexity', 'AdditiveComplexity', 'automatic', 'Bakry', 'hindrance', 'Hindrance',
      'Perron', 'NIEP', 'general_position', 'GeneralPosition', 'gp_d', 'biased', 'edge_coloring_game', 'EdgeColoringGame',
      'game_chromatic', 'GameChromatic', 'Pfaffian', 'LyndonHochschild', 'small_eigen', 'cusped', 'hypergraph_cut', 'surplus',
      'Petersen', 'snark', 'Snark', 'normal_edge', 'NormalEdge', 'Z2xZ2', 'Wang', 'Hamano']
pats = ids + arx + [a.replace('.', '_') for a in arx] + kw
out = {}
for name in ['leanpool-tree.json', 'omega-tree.json']:
    o = json.loads((D / 'sources' / name).read_text())
    paths = [e['path'] for e in o.get('tree', [])]
    hits = {p: [x for x in paths if re.search(re.escape(p), x, re.I)][:15] for p in pats}
    out[name] = {'entries': len(paths), 'truncated': o.get('truncated'), 'sha': o.get('sha'),
                 'hits': {k: v for k, v in hits.items() if v}}
cached = D.parent / 'fresh-corpus-r10' / 'sources' / 'registry-preprints.json'
if cached.exists():
    txt = cached.read_text()
    out['openai-math-cached-preprints'] = {'file': str(cached), 'hits': {p: len(re.findall(re.escape(p), txt, re.I)) for p in pats if re.search(re.escape(p), txt, re.I)}}
(D / 'outputs' / 'registry-path-screen.json').write_text(json.dumps(out, indent=1) + '\n')
for k, v in out.items():
    print(k, {kk: (vv if not isinstance(vv, dict) else {a: (b[:4] if isinstance(b, list) else b) for a, b in vv.items()}) for kk, vv in v.items()})
