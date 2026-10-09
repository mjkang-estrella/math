import concurrent.futures,datetime,hashlib,json,pathlib,urllib.request
ROOT=pathlib.Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i13_fresh_discovery'
PIN=json.loads((ROOT/'sources/upstream.json').read_text())['commit']
INPUTS=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/TEN-FINDINGS.md','frontier/README.md','frontier/OUTCOME.md','frontier/iterations/README.md','frontier/scouts/discrete.md','frontier/iterations/i07-structures.md','frontier/iterations/i05-crossfield.md','frontier/iterations/i07-parent-probability-screen.md','frontier/iterations/i09-potts-fiid-screen.md','frontier/iterations/i12-sphere-stability-screen.md','frontier/iterations/iteration13-fresh-discovery-task.json']
def sha(b):return hashlib.sha256(b).hexdigest()
inputs=[]
for p in INPUTS:
 b=(ROOT/p).read_bytes(); t=OUT/'inputs'/p;t.parent.mkdir(parents=True,exist_ok=True)
 if not t.exists():t.write_bytes(b)
 inputs.append({'path':p,'sha256':sha(t.read_bytes()),'snapshot':str(t.relative_to(ROOT))})
(OUT/'input-snapshots.json').write_text(json.dumps(inputs,indent=2)+'\n')
d=json.loads((ROOT/'sources/preprints-tree.json').read_text()); assert len(d['tree'])==13223 and d['truncated'] is False
# Every entry is inspected, not a truncated listing. Record whole tree unchanged above.
keys=['Triple-ergodic-averages-with-distinct-integer-slopes','Sidorenko','uniform-influence-bound','Sharp-Threshold-Bound','Rokhlins','Pointwise-Multiple','Pointwise-convergence-of-fourfold','Pointwise-convergence-of-triple','Common-Integer','common-bases-of-two','Cell-Bounded','Exact-Uniform-Sampling-of-Contingency','Graph-Decompositions-at','Integral-and-fractional','discrete-convexity']
selected=[];inventory=[]
for x in d['tree']:
 matches=[k for k in keys if k in x['path']]
 inventory.append({'path':x['path'],'type':x['type'],'sha':x['sha'],'selected_families':matches})
 if matches and x['type']=='blob' and x['path'].endswith(('.tex','.bib')) and '/tools/' not in x['path']:selected.append(x)
(OUT/'complete-inventory-screen.json').write_text(json.dumps({'entries':len(inventory),'truncated':False,'entries_screened':inventory},indent=2)+'\n')
def get(x):
 p=x['path'];u=f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}';t=OUT/'pinned'/p;t.parent.mkdir(parents=True,exist_ok=True)
 if not t.exists():
  with urllib.request.urlopen(u,timeout=45) as r:b=r.read()
  t.write_bytes(b)
 b=t.read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert git==x['sha'],p
 return {'upstream_path':p,'url':u,'git_blob':git,'sha256':sha(b),'bytes':len(b),'local_path':str(t.relative_to(ROOT)),'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
with concurrent.futures.ThreadPoolExecutor(max_workers=10) as pool: rows=list(pool.map(get,selected))
(OUT/'pinned-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'all_entries_read':len(inventory),'downloaded_verified':len(rows),'manuscripts':len(set(x['upstream_path'].split('/')[1] for x in rows))}))
