import pathlib,json,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
for a in ['1808.01008v1','2106.12065','2312.11951','1912.10341','2101.04561']:
 get(a+'.html','https://arxiv.org/html/'+a)
for a in ['1807.05181','1808.04191','1808.05213','1904.04071','1904.07946','1904.09841','1909.09381','2008.02163','2008.09828','2012.00396','2102.00105','2108.03567','2210.11117']:
 get(a+'-abs.html','https://arxiv.org/abs/'+a)
sha=json.loads((D/'sources/omega-head.json').read_text())['sha']
get('omega-tree.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}?recursive=1')
get('aval.pdf','https://dmtcs.episciences.org/14768/pdf')
