"""Read-only offline I55 replay. Integrity and finite diagnostics, not proof certification."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,re
R=Path(__file__).resolve().parents[3]; S=Path('frontier/sources/i55_sharp_entropy_stability_r2'); E=Path('frontier/experiments/i55_sharp_entropy_stability_r2')
A=Path('frontier/sources/i53_sharp_entropy_stability_discovery'); C=Path('frontier/sources/i14_spectral_width_novelty_r3/corpus')
REPORT=Path('frontier/reviews/i55-sharp-entropy-stability-r2.md')
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
failures=[];drift=[];counts={}
def read(p):return (R/p).read_bytes()
def record(p):return json.loads(read(p))
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def check(x,msg):
 if not x:failures.append(msg)
def run(args):return subprocess.run(args,cwd=R,capture_output=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
def verify():
 seal=record(S/'seal.json');exclude={str(S/'seal.json'),str(S/'verification.json')}
 actual={str(REPORT)}
 for d in (S,E):actual.update(str(p.relative_to(R)) for p in (R/d).rglob('*') if p.is_file() and str(p.relative_to(R)) not in exclude)
 check(actual==set(seal['files']),'I55 sealed inventory')
 for p,h in seal['files'].items():check(sha(read(p))==h,'I55 seal hash: '+p)
 counts['sealed_artifacts']=len(seal['files'])
 inputs=record(S/'inputs.json')
 for x in inputs:
  check(sha(read(x['frozen']))==x['sha256'],'frozen input: '+x['path'])
  if sha(read(x['path']))!=x['sha256']:
   if x['path'] in MUTABLE:drift.append(x['path'])
   else:failures.append('immutable live input: '+x['path'])
 counts['frozen_inputs']=len(inputs)
 author=record(S/'author-files.json')
 for p,h in author.items():check(sha(read(p))==h,'author artifact changed: '+p)
 counts['unchanged_author_artifacts']=len(author)
 # Preserve historical failures as failures, not as refreshed author evidence.
 old=record(S/'inputs/author-records/verification-initial.json')
 check(old['status']=='FAIL' and 'full corpus path inventory' in old['failures'],'historical author failure missing')
 for p in (R/S/'inputs/author-records').iterdir():check(p.read_bytes()==read(A/p.name),'archived author record: '+p.name)
 tree=record(S/'inputs/sources/preprints-tree.json');check(not tree.get('truncated',False),'truncated authoritative tree')
 check(len(tree['tree'])==13223,'complete tree size')
 manuscripts=sorted({x['path'].split('/')[1] for x in tree['tree'] if x['path'].startswith('preprints/')})
 check(manuscripts==record(S/'manuscripts.json') and len(manuscripts)==749,'complete manuscript inventory')
 blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
 counts.update(complete_tree_entries=len(tree['tree']),manuscripts=len(manuscripts))
 inventory=record(S/'corpus-inventory.json');r=run(['rg','--files','--no-ignore',str(C)])
 check(r.returncode==0 and not r.stderr,'full no-ignore inventory command')
 check(sorted(r.stdout.decode().splitlines())==sorted(p for p,h in inventory),'full corpus file multiset')
 for p,h in inventory:
  b=read(p);check(sha(b)==h,'corpus hash: '+p)
  relative=str(Path(p).relative_to(C));check(blob(b)==blobs.get(relative),'corpus Git blob: '+relative)
 check(len(inventory)==9340,'corpus count');counts['corpus_files_git_verified']=len(inventory)
 searches=record(S/'searches.json');counts['search_line_multisets']={}
 for x in searches:
  r=run(['rg','--no-ignore','-n','-i',x['pattern'],str(C)])
  check(r.returncode==x['returncode'] and r.stderr.decode()==x['stderr'],'corpus search process: '+x['name'])
  lines=sorted(r.stdout.decode().splitlines());check(lines==record(S/(x['name']+'-multiset.json')),'corpus search multiset: '+x['name'])
  check(len(lines)==x['hits'],'corpus multiplicity: '+x['name']);counts['search_line_multisets'][x['name']]=len(lines)
 pins=record(S/'inputs/author-records/pinned-manifest.json')
 for x in pins:
  b=read(A/'pinned'/x['path']);check(sha(b)==x['sha256'] and blob(b)==x['git_blob']==blobs.get(x['path']),'pin: '+x['path'])
  check('/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url'],'unpinned URL')
 counts['pinned_blobs']=len(pins)
 passages=record(S/'passages.json')
 for x in passages:
  lines=read(x['path']).decode().splitlines(keepends=True)
  check(1<=x['first_line']<=x['last_line']<=len(lines),'passage range: '+x['path'])
  check(sha(''.join(lines[x['first_line']-1:x['last_line']]).encode())==x['sha256'],'passage: '+x['path'])
 counts['passages']=len(passages)
 literature=record(S/'literature/manifest.json');pdfs=0;errors=[]
 for x in literature:
  if 'error' in x:errors.append({'name':x['name'],'error':x['error']})
  if 'path' in x:check(sha(read(x['path']))==x['sha256'],'fresh primary: '+x['name'])
  if 'extraction' in x:
   ex=x['extraction'];r=run(['pdftotext','-layout',x['path'],'-'])
   check(r.returncode==ex['returncode'] and r.stderr.decode()==ex['stderr'],'PDF process: '+x['name'])
   check(r.stdout==read(ex['path']) and sha(r.stdout)==ex['sha256'],'PDF text: '+x['name']);pdfs+=1
 counts.update(fresh_primary_requests=len(literature),fresh_pdf_replays=pdfs,retained_primary_failures=errors)
 versions={p.name:re.findall(r'\[v\d+\]',p.read_text()) for p in sorted((R/S/'literature').glob('*-abs.html'))}
 check(versions==record(S/'versions.json'),'current primary version observations')
 r=run([sys.executable,str(E/'diagnostics.py')]);check(r.returncode==0 and not r.stderr,'I55 diagnostics process')
 check(r.stdout==read(E/'diagnostics.json'),'I55 diagnostics deterministic replay')
 counts['independent_finite_assertions']=json.loads(r.stdout)['total_assertions']
 r=run([sys.executable,'frontier/experiments/i53_sharp_entropy_stability_discovery/verify.py'])
 check(r.returncode==0 and not r.stderr,'author read-only verifier process')
 original=record(S/'author-verifier-replay.json');live=json.loads(r.stdout)
 for key in ('status','counts','failures'):check(original[key]==live[key],'author verifier replay: '+key)
 counts['author_assertions_replayed']=live['counts']['diagnostic_assertions']
 counts['author_mutable_ledger_drift_informational']=live['mutable_ledger_drift_informational']
 check(len(record(S/'objections.json'))==18,'objections inventory')
try:verify()
except Exception as e:failures.append(type(e).__name__+': '+str(e))
print(json.dumps({'status':'PASS' if not failures else 'FAIL','counts':counts,'mutable_ledger_drift_informational':drift,'failures':failures,'scope':'Read-only evidence integrity and finite diagnostics; analytic verdict is in the I55 review.'},indent=2,sort_keys=True))
sys.exit(bool(failures))
