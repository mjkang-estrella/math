from fetch import fetch,D
import json,re,hashlib
x=json.loads((D/'sources/trureturing-HEAD.json').read_text());h=x['sha'];root=x['commit']['tree']['sha']
fetch(('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{root}'))
t=json.loads((D/'sources/omega-root.json').read_text())
print([(a['path'],a['sha']) for a in t['tree']])
for k in ['D5','Problems']:
 a=next(a for a in t['tree'] if a['path']==k);fetch(('omega-'+k+'.json',f"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{a['sha']}?recursive=1"))
paths=[]
for k in ['D5','Problems']:
 a=json.loads((D/f'sources/omega-{k}.json').read_text()); print(k,len(a['tree']),a['truncated']);paths += [(k+'/'+z['path'],z['sha']) for z in a['tree']]
pat=r'Fibonacci|Genocchi|Cambrian|Dixmier|Wigner|SixJ|SignedEdge|Adverse|McDiarmid|Pixed|TreeCover|Gallai|PartitionValuation|Quadrature|Involution.*Bump|NetworkDecompos'
hits=[(p,s) for p,s in paths if re.search(pat,p,re.I)]
(D/'outputs/registry-screen.json').write_text(json.dumps({'head':h,'hits':hits,'scope':'complete D5/Problems path screen only; not proof-body clearance'},indent=2)+'\n');print(hits)
