import sys,pathlib,json
sys.path.insert(0,str(pathlib.Path(sys.argv[1])/'scripts'));from fetch import fetch
D=pathlib.Path(sys.argv[1])
urls=[('https://arxiv.org/abs/2511.00650','attractors-new-abs'),('https://arxiv.org/html/2511.00650','attractors-new-body'),('https://link.springer.com/article/10.1007/s00009-024-02782-2','vor-groups'),('https://api.github.com/repos/yuhaolei-ctrl/Triangular-Lattice-Coulomb-Lean/commits/HEAD','coulomb-head'),('https://raw.githubusercontent.com/yuhaolei-ctrl/Triangular-Lattice-Coulomb-Lean/HEAD/README.md','coulomb-readme')]
for u,l in urls:fetch(u,l)
# Current complete scopes instead of truncated tree.
o=json.loads((D/'sources/the-omega-institute-trureturing-tree/body').read_text())
sha=json.loads((D/'sources/the-omega-institute-trureturing-head/body').read_text())['sha']
for path,label in [('Blueprint/D5','omega-d5'),('Problems','omega-problems')]:
 e=next((x for x in o['tree'] if x['path']==path),None)
 if e:fetch('https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+e['sha']+'?recursive=1',label)
