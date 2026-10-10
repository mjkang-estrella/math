"""Offline READ-ONLY evidence verification. Does not certify a universal theorem."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
ROOT=Path(__file__).resolve().parents[3]
S=Path('frontier/sources/i56_sharp_entropy_stability_novelty')
E=Path('frontier/experiments/i56_sharp_entropy_stability_novelty')
REPORT=Path('frontier/reviews/i56-sharp-entropy-stability-novelty.md')
C=Path('frontier/sources/i14_spectral_width_novelty_r3/corpus')
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
failures=[];drift=[];counts={}
def read(p):return (ROOT/p).read_bytes()
def rec(p):return json.loads(read(p))
def sha(b):return hashlib.sha256(b).hexdigest()
def check(ok,msg):
 if not ok:failures.append(msg)
def run(args):return subprocess.run(args,cwd=ROOT,capture_output=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},timeout=90)
def verify():
 seal=rec(S/'seal.json');exclude={str(S/'seal.json'),str(S/'verification.json')}
 actual={str(REPORT)}
 for d in [S,E]:actual.update(str(p.relative_to(ROOT)) for p in (ROOT/d).rglob('*') if p.is_file() and str(p.relative_to(ROOT)) not in exclude)
 check(actual==set(seal['files']),'I56 sealed artifact inventory')
 for p,h in seal['files'].items():check(sha(read(p))==h,'I56 sealed digest '+p)
 counts['sealed_artifacts']=len(seal['files'])
 ins=rec(S/'inputs.json')
 for x in ins:
  check(sha(read(x['frozen']))==x['sha256'],'frozen '+x['path'])
  if sha(read(x['path']))!=x['sha256']:
   if x['path'] in MUTABLE:drift.append(x['path'])
   else:failures.append('immutable live input '+x['path'])
 counts['frozen_inputs']=len(ins)
 task=rec(S/'inputs/frontier/iterations/iteration56-sharp-entropy-stability-novelty-task.json')
 check(read(S/'brief.txt').decode()=='Act as the review sub-agent for this task.\n\n'+task['brief']+'\n','exact review brief')
 old=rec(S/'author-evidence-hashes.json')
 for p,h in old:check(sha(read(p))==h,'unmodified original evidence '+p)
 counts['unmodified_author_evidence_files']=len(old)
 history=rec(S/'inputs/frontier/sources/i53_sharp_entropy_stability_discovery/verification-initial.json')
 check(history['status']=='FAIL' and 'full corpus path inventory' in history['failures'],'retained author inventory-order FAIL')
 tree=rec(S/'inputs/sources/preprints-tree.json');check(not tree.get('truncated',False),'tree is complete')
 check(len(tree['tree'])==13223,'complete tree cardinality');counts['tree_entries']=len(tree['tree'])
 roots=sorted(set(x['path'].split('/')[1] for x in tree['tree'] if x['path'].startswith('preprints/')))
 check(roots==rec(S/'manuscripts.json') and len(roots)==749,'749-manuscript inventory');counts['manuscripts']=len(roots)
 blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
 pins=rec(S/'pinned-manifest.json')
 for x in pins:
  b=read(x['local']);git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  check(git==x['git_blob']==blobs.get(x['path']),'Git blob '+x['path']);check(sha(b)==x['sha256'],'pinned digest '+x['path'])
  check('/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url'],'immutable pinned URL')
 counts['pinned_blobs']=len(pins)
 inv=rec(S/'corpus-inventory.json');r=run(['rg','--files','--no-ignore',str(C)])
 paths=sorted(str(Path(p).relative_to(C)) for p in r.stdout.decode().splitlines())
 check(r.returncode==0 and not r.stderr,'corpus inventory process');check(paths==sorted(x[0] for x in inv) and len(inv)==9340,'9340-file inventory')
 for p,h in inv:check(sha(read(C/p))==h,'corpus digest '+p)
 counts['corpus_files']=len(inv);counts['corpus_search_line_multisets']={}
 for x in rec(S/'searches.json'):
  r=run(x['args']);lines=sorted(r.stdout.decode().splitlines())
  check(r.returncode==x['returncode'] and r.stderr.decode()==x['stderr'],'search process '+x['name'])
  check(lines==rec(S/(x['name']+'-multiset.json')) and len(lines)==x['hits'],'sorted LINE MULTISET '+x['name']);counts['corpus_search_line_multisets'][x['name']]=len(lines)
 requests=[]
 for mf in ['manifest.json','manifest-additional.json']:requests+=rec(S/'literature'/mf)
 pdfs=0;failed=[]
 for x in requests:
  if 'path' in x:check(sha(read(x['path']))==x['sha256'],'primary response '+x['name'])
  if 'error' in x:failed.append({'name':x['name'],'error':x['error']})
  if x.get('extraction'):
   a=x['extraction'];check(sha(read(a['path']))==a['sha256'],'primary extraction '+x['name']);r=run(['pdftotext','-layout',x['path'],'-'])
   check(r.returncode==a['returncode'] and r.stderr.decode()==a['stderr'] and r.stdout==read(a['path']),'PDF replay '+x['name']);pdfs+=1
 counts['primary_requests']=len(requests);counts['pdf_text_replays']=pdfs;counts['preserved_current_retrieval_failures']=failed
 passages=rec(S/'passages.json')
 for x in passages:
  lines=read(x['path']).decode().splitlines(keepends=True);a,b=x['first_line'],x['last_line'];check(1<=a<=b<=len(lines),'passage bounds '+x['path']);content=''.join(lines[a-1:b]);check(content==x['passage'] and sha(content.encode())==x['sha256'],'actual passage '+x['path'])
 counts['actual_passages']=len(passages)
 r=run([sys.executable,str(E/'diagnostics.py')]);check(r.returncode==0 and not r.stderr,'independent diagnostics process');check(r.stdout==read(E/'diagnostics.json'),'independent exact diagnostic replay');counts['independent_assertions']=json.loads(r.stdout)['assertions']
 r=run([sys.executable,'frontier/experiments/i53_sharp_entropy_stability_discovery/verify.py']);check(r.returncode==0 and not r.stderr,'original author verifier process');live=json.loads(r.stdout);frozen=rec(S/'author-verifier-replay.json')
 check(live['status']=='PASS' and not live['failures'],'original author evidence replay status');check(live['counts']==frozen['counts'],'original author immutable counts')
 check(set(live['mutable_ledger_drift_informational'])<=MUTABLE,'only four informational ledgers')
 counts['author_replay']=live
try:verify()
except Exception as e:failures.append(type(e).__name__+': '+str(e))
print(json.dumps({'status':'PASS' if not failures else 'FAIL','counts':counts,'mutable_ledger_drift_informational':sorted(drift),'failures':failures,'scope':'I56 evidence integrity, exact finite diagnostics and unchanged I53 evidence replay; universal mathematical argument is in review §§2–3; no original-proof or count decision.'},indent=2,sort_keys=True))
sys.exit(bool(failures))
