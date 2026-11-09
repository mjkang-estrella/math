from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
R=Path(__file__).resolve().parents[1]; root=R.parents[3]; tree=json.loads((root/'sources/preprints-tree.json').read_text()); entries={x['path']:x for x in tree['tree']}; pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
selected={
'353': [('Smooth-Nonquadratic-Affine-Maximal-Graph-in-Dimension-Ten-October-5-2026','build/source/main.tex'),('The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026','build/main.tex'),('The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026','build/sections/rigidity.tex')],
'071':[('Removable-Boundaries-and-Rigidity-of-Circle-Domains-September-23-2026','build/sections/introduction.tex'),('Removable-Boundaries-and-Rigidity-of-Circle-Domains-September-23-2026','build/sections/rigidity.tex'),('Koebes-Circle-Domain-Conjecture-September-23-2026','build/sections/00-introduction.tex')],
'262':[('Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026','build/sections/introduction.tex'),('Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026','build/sections/rigidity.tex'),('Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials-October-5-2026','build/sections/introduction.tex')]
}
def get(item):
 n,i,d,f=item;p='preprints/'+d+'/'+f;e=entries[p];u='https://raw.githubusercontent.com/openai/math/'+pin+'/'+p;out=R/'packet/private/upstream'/n/(str(i)+'-'+Path(f).name);out.parent.mkdir(parents=True,exist_ok=True)
 try:
  b=urllib.request.urlopen(u,timeout=45).read();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==e['sha'];out.write_bytes(b);return {'family':n,'path':p,'url':u,'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'local':str(out.relative_to(R/'packet')),'tree_entry':e,'status':'ok'}
 except Exception as ex:return {'url':u,'status':'failed','error':str(ex)}
items=[(n,i,d,f) for n,v in selected.items() for i,(d,f) in enumerate(v)]
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: results=list(pool.map(get,items))
(R/'packet/private/upstream/receipts.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps([{k:v for k,v in x.items() if k in ['family','local','bytes','status','error']} for x in results],indent=2))
