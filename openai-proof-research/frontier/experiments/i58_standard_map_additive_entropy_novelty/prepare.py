"""One-time I58 evidence collection; writes only the assigned I58 evidence roots."""
from pathlib import Path
import json,hashlib,subprocess,urllib.request,urllib.error,datetime,concurrent.futures
R=Path.cwd(); S=R/'frontier/sources/i58_standard_map_additive_entropy_novelty'
def sha(b): return hashlib.sha256(b).hexdigest()
def dump(p,x): p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
mutable=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
inputs=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md',*mutable,'frontier/iterations/iteration58-standard-map-additive-entropy-novelty-task.json','frontier/iterations/i52-ergodic-dynamical-discovery.md','frontier/iterations/i54-standard-map-additive-entropy.md','frontier/experiments/i52-parent-verification.json','frontier/experiments/i54-parent-verification.json']
for pref in ['i52_ergodic_dynamical_discovery','i54_standard_map_additive_entropy']:
 for name in ['brief.txt','objections.txt','objections-and-responses.txt','source-contracts.json','passages.json','pinned-manifest.json','seal.json']:
  p=f'frontier/sources/{pref}/{name}'
  if (R/p).exists(): inputs.append(p)
 for name in ['verify.py','diagnostics.py','diagnostics.json']:
  inputs.append(f'frontier/experiments/{pref}/{name}')
manifest=[]
for p in inputs:
 b=(R/p).read_bytes(); dest=S/'inputs'/p; dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 manifest.append({'path':p,'sha256':sha(b),'mutable_ledger':p in mutable})
dump(S/'inputs-manifest.json',manifest)
task=json.loads((R/inputs[8]).read_text()) if False else json.loads((R/'frontier/iterations/iteration58-standard-map-additive-entropy-novelty-task.json').read_text())
(S/'brief.txt').write_text('Act as the review sub-agent for this task.\n\n'+task['brief'])
pins=json.loads((R/'frontier/sources/i54_standard_map_additive_entropy/pinned-manifest.json').read_text())
for p in pins:
 b=(R/'frontier/sources/i54_standard_map_additive_entropy/pinned'/p['path']).read_bytes(); assert sha(b)==p['sha256'];dest=S/'pinned'/p['path'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
dump(S/'pinned-manifest.json',pins)
corpus=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
files=sorted(subprocess.check_output(['rg','--files','--no-ignore',str(corpus)],text=True).splitlines())
tree=json.loads((R/'sources/preprints-tree.json').read_text())['tree']; tree_by={x['path']:x for x in tree}
inventory=[]
for f in files:
 p=Path(f);rel=p.relative_to(corpus).as_posix(); tp=rel if rel.startswith('preprints/') else 'preprints/'+rel; b=p.read_bytes(); blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==tree_by[tp]['sha'],rel
 inventory.append({'path':str(p.relative_to(R)),'tree_path':tp,'blob':blob,'sha256':sha(b)})
dump(S/'corpus-inventory.json',{'tree_entries':len(tree),'manuscripts':len({x['path'].split('/')[1] for x in tree}),'files':inventory})
searches=[]
for name,pattern in [('standard','standard[- ]map|Chirikov|Sinai.*entropy'),('projective','Dirichlet|Green.*matrix|contracting graph|small.ball|anti.concentration'),('entropy','additive.*entropy|entropy.*lower|Lyapunov.*large|avalanche|first.*crossing')]:
 args=['rg','--no-ignore','-n','-i',pattern,str(corpus.relative_to(R))]; out=subprocess.run(args,capture_output=True,text=True); assert out.returncode in [0,1]
 rows=sorted(out.stdout.splitlines());dump(S/(name+'-search.json'),rows);searches.append({'name':name,'args':args,'lines':len(rows),'result':name+'-search.json'})
dump(S/'searches.json',searches)
prior=json.loads((R/'frontier/sources/i54_standard_map_additive_entropy/responses.json').read_text())
requests=[(x['name'],x['url'],x['path']) for x in prior]
requests += [('pin-scales',next(x['url'] for x in pins if x['path'].endswith('/scales.tex')),'literature/pin-scales.tex'),('dk-survey','https://silviusklein.github.io/research/DK-survey16.pdf','literature/dk-survey.pdf')]
def fetch(x):
 name,url,path=x; rec={'name':name,'url':url,'retrieved':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':path}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 I58 scholarly review'}),timeout=45) as f: b=f.read();rec.update(status=f.status,final_url=f.url,content_type=f.headers.get('Content-Type'))
 except urllib.error.HTTPError as e: b=e.read();rec.update(status=e.code,final_url=e.url,error=str(e))
 except Exception as e: b=str(e).encode();rec.update(status=None,error=str(e))
 dest=S/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b);rec['sha256']=sha(b);return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool: responses=list(pool.map(fetch,requests))
dump(S/'responses.json',responses)
pdfs=[]
for r in responses:
 if r['path'].endswith('.pdf') and (S/r['path']).read_bytes().startswith(b'%PDF'):
  out=subprocess.check_output(['pdftotext','-layout',str(S/r['path']),'-']);path=r['path'][:-4]+'.txt';(S/path).write_bytes(out);pdfs.append({'pdf':r['path'],'text':path,'sha256':sha(out)})
dump(S/'pdf-extractions.json',pdfs)
print(json.dumps({'inputs':len(manifest),'pins':len(pins),'corpus':len(files),'searches':[(x['name'],x['lines']) for x in searches],'responses':[(x['name'],x['status']) for x in responses],'pdfs':len(pdfs)},indent=2))
