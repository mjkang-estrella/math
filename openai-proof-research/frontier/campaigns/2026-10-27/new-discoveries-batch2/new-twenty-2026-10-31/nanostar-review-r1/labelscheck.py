import re,json,runpy,pathlib,sys
# Execute only this review's own checker, never discovery code.
sys.argv=['mathcheck.py','check']
d=runpy.run_path(str(pathlib.Path.cwd()/'mathcheck.py'))
s=(pathlib.Path('build/lean/Certificate.lean')).read_text()
lab=list(map(int,re.search(r'def labels .*?!\[([^]]+)\]',s).group(1).split(',')))
g=d['graph'](d['A']);t=d['model'](4)
assert set(lab)==set(g) and len(lab)==88
for i in t:
 assert {lab[j] for j in t[i]}==g[lab[i]],i
print('EXACT LEAN LABEL ORDER AND ALL ADJACENCIES PASS')
