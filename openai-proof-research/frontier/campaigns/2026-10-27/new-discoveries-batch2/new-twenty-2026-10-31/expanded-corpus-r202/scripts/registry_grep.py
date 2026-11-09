"""Path/title grep of cached registry trees (Lean Pool tree + projects.yml, Omega D5/Problems, OpenAI/math HEAD file list)
for reserved-topic keywords. usage: registry_grep.py LANEDIR"""
import json, sys, pathlib, re
L = pathlib.Path(sys.argv[1])
KW = ['pancake', 'PopTsack', 'Pop_T', 'poptsack', 'torsing', 'crank', 'KanadeRussell', 'Kanade', 'Russell', 'monotonetriangle',
      'MonotoneTriangle', 'Riegler', 'VSASM', 'AlternatingSign', 'hypercellular', 'Hypercellular', 'partialcube', 'PartialCube',
      'rigged', 'Rigged', 'noncrossing', 'NonCrossing', 'kcrossing', 'Byszewski', 'Ulas', 'ThueMorse', 'Prouhet', 'digitsum', 'DigitSum',
      'pipedream', 'PipeDream', 'quarterplane', 'QuarterPlane', 'SortingNetwork', 'sortingnetwork', 'Romik', 'swapprocess',
      'Nabijou', 'Barrott', 'tangentcurve', 'Tucker', 'distinguishing', 'Distinguishing', 'Filliman', 'simplexprojection',
      'TruncatedJacobi', 'truncatedjacobi', 'GuoZeng', 'twospec', '2spec', 'Pazzis', 'eigenvalue', 'Blanco', 'Lehner']
KWL = [k.lower() for k in KW]
def scan(name, paths):
    hits = [p for p in paths if any(k in p.lower() for k in KWL)]
    print(f'== {name}: {len(paths)} paths, {len(hits)} keyword hits')
    for h in hits[:60]: print('  ', h)
lp = json.loads((L / 'sources/leanpool-tree.json').read_text())
scan('lean-pool tree (truncated=%s)' % lp.get('truncated'), [x['path'] for x in lp['tree']])
yml = (L / 'sources/leanpool-projects.yml').read_text(errors='replace').splitlines()
ids = ['1902.04055', '2106.05471', '2101.10910', '1809.08655', '1207.4437', '1606.02154', '1706.02443', '1706.07213', '1805.10569',
       '1409.8118', '1807.03044', '2005.02043', '2007.05016', '1412.0881', '2601.18436', '1205.4340', '1302.0301']
yh = [(i + 1, l.strip()) for i, l in enumerate(yml) if any(k in l.lower() for k in KWL + ids)]
print(f'== lean-pool projects.yml: {len(yml)} lines, {len(yh)} hits'); [print('  ', h) for h in yh[:60]]
for nm in ('omega-problems', 'omega-d5'):
    t = json.loads((L / f'sources/{nm}.json').read_text())
    scan(f'{nm} (truncated={t.get("truncated")})', [x['path'] for x in t['tree']])
oa = json.loads((L / 'sources/openai-head.json').read_text())
scan('openai/math HEAD commit files (%d)' % len(oa.get('files', [])), [f['filename'] for f in oa.get('files', [])])
