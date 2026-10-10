"""Offline, read-only I64 integrity/finite replay. No network, writes or seal refresh."""
from pathlib import Path
import hashlib,json,subprocess,sys,os,collections
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i64_entropy_coefficient_extraction_novelty';E=R/'frontier/experiments/i64_entropy_coefficient_extraction_novelty';REPORT=R/'frontier/reviews/i64-entropy-coefficient-extraction-novelty.md'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def get(p):return json.loads(p.read_text())
def req(v,label):
 if not v:raise AssertionError(label)
def main():
 seal=get(S/'seal.json');exclude={S/'seal.json',E/'verification.json'}
 actual={str(p.relative_to(R)) for root in [S,E] for p in root.rglob('*') if p.is_file() and p not in exclude}|{str(REPORT.relative_to(R))}
 req(actual=={r['path'] for r in seal['artifacts']},'complete own sealed inventory')
 for r in seal['artifacts']:req(sha((R/r['path']).read_bytes())==r['sha256'],'own sealed '+r['path'])
 inputs=get(S/'inputs.json')+get(S/'inflight-inputs.json');drift=[]
 for r in inputs:
  req(sha((S/'inputs'/r['path']).read_bytes())==r['sha256'],'frozen input '+r['path'])
  if r['mutable']:
   if sha((R/r['path']).read_bytes())!=r['sha256']:drift.append(r['path'])
  else:req(sha((R/r['path']).read_bytes())==r['sha256'],'immutable input '+r['path'])
 req({r['path'] for r in inputs if r['mutable']}=={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'},'only four mutable ledgers')
 task=get(S/'inputs/frontier/iterations/iteration64-entropy-coefficient-extraction-novelty-task.json')
 req((S/'brief.txt').read_text()=='Act as the review sub-agent for this task.\n\n'+task['brief'],'full original brief')
 req(get(S/'inputs/sources/upstream.json')['commit']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','upstream revision')
 tree=get(S/'inputs/sources/preprints-tree.json')['tree'];index={r['path']:r for r in tree};manuscripts=sorted({p.split('/')[1] for p in index})
 req(len(tree)==13223 and len(manuscripts)==749 and manuscripts==get(S/'manuscripts.json'),'complete tree and manuscript inventory')
 C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus';corpus=get(S/'corpus.json')
 names=sorted(p.removeprefix('./') for p in subprocess.check_output(['rg','--files','--no-ignore','.'],cwd=C,text=True).splitlines())
 req(names==sorted(r['path'] for r in corpus) and len(names)==9340,'complete ignored corpus')
 for r in corpus:
  b=(C/r['path']).read_bytes();req(sha(b)==r['sha256'] and blob(b)==r['git_blob']==index[r['path']]['sha'],'corpus hash/blob '+r['path'])
 pins=get(S/'pins.json')+get(S/'additional-pins.json')
 for r in pins:
  b=(S/'pinned'/r['path']).read_bytes();req(sha(b)==r['sha256'] and blob(b)==r['git_blob']==index[r['path']]['sha'],'selected pin')
 prior=get(S/'prior-hashes.json')
 for r in prior:req(sha((R/r['path']).read_bytes())==r['sha256'],'unchanged prior '+r['path'])
 searches=get(S/'searches.json')
 for r in searches:
  cp=subprocess.run(['rg','--no-ignore','-n','-i',r['pattern'],'.'],cwd=C,capture_output=True,text=True);req(cp.returncode in [0,1],'rg status')
  saved=get(S/'searches'/(r['label']+'.json'));req(len(saved)==r['lines'] and collections.Counter(saved)==collections.Counter(cp.stdout.splitlines()),'search line multiset '+r['label'])
 passages=get(S/'passages.json');contracts=get(S/'read-contracts.json')
 for r in passages:
  lines=(R/r['path']).read_text().splitlines(keepends=True);t=''.join(lines[r['start']-1:r['end']]);req(t==r['text'] and sha(t.encode())==r['sha256'],'passage slice')
 for r in contracts:
  req(sha((R/r['path']).read_bytes())==r['sha256'],'read contract hash')
  for a,b in r['ranges']:req(any(p['path']==r['path'] and p['start']==a and p['end']==b for p in passages),'contract passage coverage')
 primary=[]
 for f in ['manifest.json','supplement.json','bathory-manifest.json','bathory-estimates-manifest.json']:primary+=get(S/'literature'/f)
 pdfs=0
 for r in primary:
  if not r.get('path'):req('error' in r,'retained failure');continue
  req(sha((R/r['path']).read_bytes())==r['sha256'],'primary response '+r['name'])
  if r.get('text_path'):
   b=subprocess.check_output(['pdftotext','-layout',str(R/r['path']),'-']);req(b==(R/r['text_path']).read_bytes() and sha(b)==r['text_sha256'],'PDF replay '+r['name']);pdfs+=1
 for f in ['versions.json','late-versions.json']:
  for r in get(S/'literature'/f):
   t=(S/'literature'/(r['name']+'.txt')).read_text();req(sha(t.encode())==r['text_sha256'],'served text version hash')
   for v in r['arxiv_pdf_header_versions']:req(v in t,'served PDF header version')
 for r in get(S/'raw-pin-comparisons.json'):
  b=(R/r['response']).read_bytes();req(b==(R/r['pin']).read_bytes() and blob(b)==r['git_blob'],'fresh raw pin')
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');dependencies={}
 for num,stem in [(61,'averaged_entropy_coefficient_rounding'),(63,'entropy_coefficient_extraction_r2')]:
  live=json.loads(subprocess.check_output([sys.executable,f'frontier/experiments/i{num}_{stem}/verify.py'],cwd=R,env=env));saved=get(S/f'i{num}-readonly-replay.json');req(live['status']=='PASS','dependency replay PASS')
  for k,v in saved.items():
   if 'drift' not in k:req(live[k]==v,'dependency unchanged replay '+str(num)+' '+k)
  dependencies[str(num)]={'status':live['status'],'mutable_ledger_drift':live['mutable_ledger_drift']}
 b=subprocess.check_output([sys.executable,str(E/'diagnostics.py')],cwd=R,env=env);req(b==(S/'diagnostics.json').read_bytes(),'independent deterministic exact replay');d=json.loads(b)
 req(d['status']=='PASS' and d['floating_records']==0,'diagnostic scope')
 return dict(status='PASS',sealed_artifacts=len(seal['artifacts']),inputs=len(inputs),mutable_ledger_drift=drift,tree_entries=len(tree),manuscripts=len(manuscripts),corpus_files=len(corpus),selected_pins=len(pins),prior_files=len(prior),read_contracts=len(contracts),passages=len(passages),search_line_multisets=[r['lines'] for r in searches],primary_requests=len(primary),successful_primary_responses=sum(r.get('status')==200 for r in primary),primary_failures=sum(bool(r.get('error')) for r in primary),pdf_replays=pdfs,raw_pin_replays=len(get(S/'raw-pin-comparisons.json')),independent_exact_assertions=d['exact_assertions'],floating_records=0,dependency_replays=dependencies,limitation='Provenance and finite diagnostics only; I63 owns analytic PASS, I64 owns separate SUBSTANTIAL verdict; AR and U remain open. No count/priority decision.')
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True,indent=2))
 except Exception as e:print(json.dumps(dict(status='FAIL',error=str(e)),indent=2));sys.exit(1)
