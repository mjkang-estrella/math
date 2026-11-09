"""Path/title grep of registry trees for reserved-topic keywords (expanded-corpus-r204). usage: registry_grep.py LANEDIR"""
import json, sys, pathlib
L = pathlib.Path(sys.argv[1])
KW = ['nim', 'gurvich', 'naumova', 'slownim', 'slow_nim', 'nash', 'ascending', 'subgraphdecomp', 'forestpath', 'linearforest',
      'facemagic', 'face_magic', 'projectivegrid', 'curran', 'isolation', 'irredundan', 'tensor', 'frobenius', 'grothendieck', 'hafner',
      'rook', 'polyomino', 'circumference', 'clique', 'distanceenergy', 'distance_energy', 'cliquetree', 'hirschorn', 'crossintersect',
      'cross_intersect', 'ballot', 'spiro', 'derangement', 'excedance', 'rightleftmin', 'raag', 'rightangledartin', 'proportional',
      'connectivity', 'wordrepresent', 'word_represent', 'semitransitive', 'semi_transitive', 'linegraph', 'line_graph', 'oddedge',
      'odd_edge', 'shannon', 'neuralcode', 'neural_code', 'embeddingdim', 'orbifold', 'bootstrap', 'laplacian']
ids = ['2311.03257', '2312.08382', '2203.06466', '2206.03586', '2206.07208', '2206.07879', '2209.00687', '2211.05651', '2212.01989',
       '2102.10241', '2102.10277', '2103.04599', '2105.08455', '2106.03782', '2106.16242', '2108.02363', '2109.04099', '2111.01010',
       '2111.12716', '360653', '361128', '404028', '353896', '354915', '355026', '355038', '355948', '356829', '381721', '349829',
       '349831', '350025', '350721', '350925', '351162', '351536', '351888', '352460', '352733']
def norm(s): return s.lower().replace('-', '').replace(' ', '')
def scan(name, paths):
    hits = [p for p in paths if any(k in norm(p) for k in KW + ids)]
    print(f'== {name}: {len(paths)} paths, {len(hits)} keyword hits')
    for h in hits[:200]: print('  ', h)
lp = json.loads((L / 'sources/leanpool-tree.json').read_text())
scan('lean-pool tree (truncated=%s)' % lp.get('truncated'), [x['path'] for x in lp['tree']])
yml = (L / 'sources/leanpool-projects.yml').read_text(errors='replace').splitlines()
yh = [(i + 1, l.strip()) for i, l in enumerate(yml) if any(k in norm(l) for k in KW + ids)]
print(f'== lean-pool projects.yml: {len(yml)} lines, {len(yh)} hits'); [print('  ', h) for h in yh[:100]]
for nm in ('omega-problems', 'omega-d5', 'omega-reg'):
    t = json.loads((L / f'sources/{nm}.json').read_text())
    scan(f'{nm} (truncated={t.get("truncated")})', [x['path'] for x in t['tree']])
oa = json.loads((L / 'sources/openai-head.json').read_text())
scan('openai/math HEAD commit files', [f['filename'] for f in oa.get('files', [])])
