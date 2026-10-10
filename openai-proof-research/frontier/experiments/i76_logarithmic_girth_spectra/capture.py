"""One-time evidence capture. Never invoked by the offline verifier."""
import datetime, hashlib, json, pathlib, urllib.request
ROOT=pathlib.Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i76_logarithmic_girth_spectra'
OLD=ROOT/'frontier/sources/i72_graph_probability_discovery'
def sha(b): return hashlib.sha256(b).hexdigest()
def put(name,obj):
    p=S/name
    assert not p.exists(), p
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
ledgers=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
paths=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',
 'frontier/iterations/i72-graph-probability-discovery.md','frontier/experiments/i72-parent-verification.json',
 'frontier/sources/i72_graph_probability_discovery/seal-v1.json',
 'frontier/sources/i72_graph_probability_discovery/pinned-manifest.json',
 'frontier/sources/i72_graph_probability_discovery/primary-requests.json',
 'frontier/sources/i72_graph_probability_discovery/versions.json']+ledgers
put('inputs.json',[dict(path=p,sha256=sha((ROOT/p).read_bytes()),bytes=(ROOT/p).stat().st_size,mutable=p in ledgers) for p in paths])
manifest=json.loads((OLD/'pinned-manifest.json').read_text())
selected=[x for x in manifest if '/GOE-bulk-' in x['path'] or '/Fixed-energy-universality-for-weak-' in x['path']]
put('source-references.json',[dict(x,local_path=str((OLD/'pinned'/x['path']).relative_to(ROOT))) for x in selected])
requests=[('hy-current.html','https://arxiv.org/abs/2102.00963',None),
 ('hy-v3.pdf','https://arxiv.org/pdf/2102.00963v3',OLD/'primary/hy-v3.pdf'),
 ('mww.pdf','https://users.monash.edu/~nwormald/papers/girth.pdf',OLD/'primary/mww.pdf')]
for prefix,end in [('GOE-bulk','02-preliminaries.tex'),('Fixed-energy','03-local-law.tex')]:
    x=next(x for x in selected if x['path'].split('/')[1].startswith(prefix) and x['path'].endswith(end))
    requests.append((prefix+'.tex',x['raw_url'],OLD/'pinned'/x['path']))
records=[]
for name,url,old in requests:
    rec=dict(name=name,url=url,requested_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I76-research-evidence/1.0'}),timeout=45) as r:
            data=r.read(); rec.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=sha(data),bytes=len(data))
        if old and data==old.read_bytes():
            rec['body_reference']=str(old.relative_to(ROOT)); rec['fresh_matches_old']=True
        else:
            p=S/'responses'/name; p.parent.mkdir(exist_ok=True); assert not p.exists();p.write_bytes(data)
            rec['body_reference']=str(p.relative_to(ROOT)); rec['fresh_matches_old']=False
    except Exception as e: rec['error']=repr(e)
    records.append(rec)
put('fresh-responses.json',records)
print(json.dumps([{'name':r['name'],'status':r.get('status'),'sha256':r.get('sha256'),'error':r.get('error')} for r in records],indent=2))
