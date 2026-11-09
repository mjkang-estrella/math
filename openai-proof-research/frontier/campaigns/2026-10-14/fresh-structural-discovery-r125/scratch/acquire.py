import pathlib,json,hashlib,urllib.request,concurrent.futures
R=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); O=R/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r125'; pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads((R/'sources/preprints-tree.json').read_text()); assert len(tree['tree'])==13223 and tree['truncated'] is False
sel=[]
for e in tree['tree']:
 p=e['path']
 if e['type']!='blob' or not p.endswith('.tex'): continue
 if 'Infinite-Matroid-Packing' in p and ('/sections/' in p or p.endswith('/paper.tex')): sel.append(e)
 if 'Almost-Linear-Time-Maximum' in p and any(p.endswith(x) for x in ['01-introduction.tex','10-f-factors.tex']): sel.append(e)
 if 'FPRAS-for-Common-Integer' in p and any(p.endswith(x) for x in ['introduction.tex','polyhedra.tex','counting.tex','main.tex']): sel.append(e)
def f(e):
 u='https://raw.githubusercontent.com/openai/math/'+pin+'/'+e['path']; b=urllib.request.urlopen(u,timeout=45).read(); assert len(b)==e['size']; assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']; dst=O/'packet/private/upstream'/e['path']; dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(b); return dict(canonical=e,url=u,local=str(dst.relative_to(O/'packet')),sha256=hashlib.sha256(b).hexdigest())
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex: records=list(ex.map(f,sel))
(O/'packet/private/upstream-register.json').write_text(json.dumps(records,indent=2)+'\n'); print('canonical bodies',len(records))
