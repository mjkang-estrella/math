"""Path screen of Lean Pool (full tree at pinned HEAD), Omega D5 + Problems (complete recursive subtrees at HEAD)
and the cached OpenAI/math preprints listing, for the 20 reserved IDs, their source arXiv IDs and topic keywords.
Writes outputs/registry-screen.json.  Usage: registry_screen.py LANE OPENAI_PREPRINTS_JSON"""
import sys, json, pathlib, re, hashlib
D = pathlib.Path(sys.argv[1]).resolve(); S = D / 'sources'
res = json.loads((D / 'reservation.json').read_text())
ids = [str(i) for i in res['ids']]
arx = sorted({r['source_url'].rsplit('/', 1)[1] for r in res['rows']})
arx_dash = [a.replace('.', '_') for a in arx] + [a.replace('.', '') for a in arx]
kw = ['polar', 'cograph', 'Cograph', 'Contreras', 'Hernandez', 'antimagic', 'Antimagic', 'Kamatchi', 'Arumugam',
      'betweenness', 'Betweenness', 'blowup', 'BlowUp', 'independence_equiv', 'IndependenceEquiv', 'independencePoly',
      'relative_clique', 'RelativeClique', 'colored_mixed', 'ColoredMixed', 'DCI', 'dihedral', 'Dihedral',
      'Spinoza', 'deck', 'Deck', 'chromatic_symmetric', 'ChromaticSymmetric', 'Stanley', 'hero', 'Hero',
      'dichromatic', 'Dichromatic', 'Bessel', 'Hankel', 'fishnet', 'Basso', 'toric', 'Toric', 'chord_diagram',
      'ChordDiagram', 'terminal', 'graph_product', 'GraphProduct', 'Gray', 'braided', 'Braided', 'cameral',
      'distance_graph', 'DistanceGraph', 'Zapletal']
def paths_of(f, prefix=''):
    o = json.loads((S / f).read_text())
    return [prefix + t['path'] for t in o['tree']], bool(o.get('truncated'))
lp, lpt = paths_of('leanpool-tree.json')
d5, d5t = paths_of('omega-D5-tree.json', 'D5/')
pr, prt = paths_of('omega-Problems-tree.json', 'Problems/')
oa = json.loads(pathlib.Path(sys.argv[2]).read_text())
oa_paths = []
def walk(x):
    if isinstance(x, dict):
        for k, v in x.items():
            if k in ('path', 'name') and isinstance(v, str): oa_paths.append(v)
            walk(v)
    elif isinstance(x, list):
        for v in x: walk(v)
    elif isinstance(x, str) and '/' in x: oa_paths.append(x)
walk(oa)
pats = ids + arx + arx_dash + kw
def grep(paths):
    h = {}
    for k in pats:
        m = [p for p in paths if re.search(re.escape(k), p)]
        if m: h[k] = {'count': len(m), 'examples': m[:6]}
    return h
heads = {}
for f in ['leanpool-head.json', 'omega-head.json', 'openai-math-head.json']:
    o = json.loads((S / f).read_text()); r = json.loads((S / (f + '.receipt.json')).read_text())
    heads[f] = {'url': r['url'], 'utc': r['utc'], 'sha': o.get('sha'), 'date': o['commit']['committer']['date']}
gh = {}
for p in sorted(S.glob('gh-search-*.json')):
    if p.name.endswith('.receipt.json'): continue
    o = json.loads(p.read_text()); r = json.loads((S / (p.name + '.receipt.json')).read_text())
    gh[p.name] = {'url': r['url'], 'status': r.get('status'), 'utc': r['utc'], 'total_count': o.get('total_count'),
                  'items': [(it['full_name'], (it.get('description') or '')[:160]) for it in o.get('items', [])[:10]]}
out = {'patterns': pats, 'registry_heads': heads,
       'leanpool': {'paths': len(lp), 'truncated': lpt, 'hits': grep(lp)},
       'omega_D5': {'paths': len(d5), 'truncated': d5t, 'hits': grep(d5)},
       'omega_Problems': {'paths': len(pr), 'truncated': prt, 'hits': grep(pr)},
       'openai_math_preprints_cached': {'file': sys.argv[2], 'sha256': hashlib.sha256(pathlib.Path(sys.argv[2]).read_bytes()).hexdigest(),
                                        'paths': len(oa_paths), 'hits': grep(oa_paths)},
       'github_repository_search': gh,
       'note': 'Path/name screens only, not proof-body reading. Lean Pool projects.yml was 404 at the repo root at the pinned sha; '
               'the complete non-truncated Lean Pool tree was grepped instead. OpenAI/math HEAD unchanged from the cached listing.'}
(D / 'outputs' / 'registry-screen.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
for k in ['leanpool', 'omega_D5', 'omega_Problems', 'openai_math_preprints_cached']:
    print(k, out[k]['paths'], out[k].get('truncated'), {kk: v['count'] for kk, v in out[k]['hits'].items()})
print(heads)
