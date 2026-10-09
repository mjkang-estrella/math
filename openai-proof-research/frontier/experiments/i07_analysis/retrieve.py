import json,hashlib,pathlib,urllib.request,concurrent.futures,datetime
R=pathlib.Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i07_analysis'
keys=['Weak-MTW','diffeomorphic-approximation','One-Third-Stability','Bounded-Measurable-Scalar','one-boundary-patch','One-Boundary-Patch']
tree=json.loads((R/'sources/preprints-tree.json').read_text())['tree']
paths=[x for x in tree if any(k in x['path'] for k in keys) and x['path'].endswith('.tex')]
rev=json.loads((R/'sources/upstream.json').read_text())['commit']
def get(e):
 p=e['path']; u=f'https://raw.githubusercontent.com/openai/math/{rev}/{p}'; b=urllib.request.urlopen(u).read(); f=S/'upstream'/p.removeprefix('preprints/'); f.parent.mkdir(parents=True,exist_ok=True); f.write_bytes(b)
 return dict(path=p,url=u,local=str(f.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),git_blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),expected_blob=e['sha'],bytes=len(b))
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex: out=list(ex.map(get,paths))
(S/'retrieval-manifest.json').write_text(json.dumps(dict(revision=rev,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sources=out),indent=2)+'\n')
inputs=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/README.md','frontier/iterations/README.md','frontier/scouts/analysis.md','frontier/reviews/hotspots-polygon-novelty-r3.md','frontier/iterations/i05-crossfield.md','frontier/reviews/i05-crossfield-r2.md']
(S/'input-snapshot.json').write_text(json.dumps({p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in inputs},indent=2)+'\n')
print(len(out),'sources; all blob hashes match:',all(e['git_blob']==e['expected_blob'] for e in out))
