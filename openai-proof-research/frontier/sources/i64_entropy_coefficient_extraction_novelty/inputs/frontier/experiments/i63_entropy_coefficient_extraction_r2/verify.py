"""Offline read-only I63 integrity and independent finite-diagnostic verifier.
It never refreshes a seal, downloads a response, or writes a diagnostic result.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,os,collections,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i63_entropy_coefficient_extraction_r2';E=R/'frontier/experiments/i63_entropy_coefficient_extraction_r2';REPORT=R/'frontier/reviews/i63-entropy-coefficient-extraction-r2.md'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def get(p):return json.loads(p.read_text())
def req(v,label):
 if not v:raise AssertionError(label)
def main():
 seal=get(S/'seal.json');excluded={S/'seal.json',E/'verification.json'}
 actual={str(p.relative_to(R)) for folder in [S,E] for p in folder.rglob('*') if p.is_file() and p not in excluded}|{str(REPORT.relative_to(R))}
 req(actual=={r['path'] for r in seal['artifacts']},'complete own sealed inventory')
 for r in seal['artifacts']:req(sha((R/r['path']).read_bytes())==r['sha256'],'own seal '+r['path'])
 drift=[];inputs=get(S/'inputs.json')
 for r in inputs:
  req(sha((R/r['frozen']).read_bytes())==r['sha256'],'frozen input')
  live=sha((R/r['path']).read_bytes())
  if r['mutable']:
   if live!=r['sha256']:drift.append(r['path'])
  else:req(live==r['sha256'],'immutable input '+r['path'])
 req({r['path'] for r in inputs if r['mutable']}=={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'},'exactly permitted mutable ledgers')
 task=get(S/'inputs/frontier/iterations/iteration63-entropy-coefficient-extraction-r2-task.json')
 req((S/'brief.txt').read_text()=='Act as the review sub-agent for this task.\n\n'+task['brief'],'full frozen original task')
 upstream=get(S/'inputs/sources/upstream.json');req(upstream['commit']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','immutable upstream revision')
 tree=get(S/'inputs/sources/preprints-tree.json')['tree'];index={r['path']:r for r in tree}
 req(len(tree)==13223 and len({p.split('/')[1] for p in index})==749,'complete tree and manuscript inventory')
 C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus';corpus=get(S/'corpus.json')
 actual=sorted(n.removeprefix('./') for n in subprocess.check_output(['rg','--files','--no-ignore','.'],cwd=C,text=True).splitlines())
 req(actual==sorted(r['path'] for r in corpus) and len(actual)==9340,'complete ignored corpus inventory')
 for r in corpus:
  b=(C/r['path']).read_bytes();req(sha(b)==r['sha256'] and blob(b)==r['git_blob']==index[r['path']]['sha'],'corpus SHA and Git '+r['path'])
 pins=get(S/'pins.json')
 for r in pins:
  b=(R/r['frozen']).read_bytes();req(sha(b)==r['sha256'] and blob(b)==r['git_blob']==index[r['upstream_path']]['sha'],'pin blob')
  req((R/r['path']).read_bytes()==b,'original pin unchanged')
 prior=get(S/'prior-hashes.json')
 for r in prior:req(sha((R/r['path']).read_bytes())==r['sha256'],'prior unchanged '+r['path'])
 for r in get(S/'prior-records.json'):req(sha((R/r['frozen']).read_bytes())==sha((R/r['path']).read_bytes())==r['sha256'],'individual prior brief/objections')
 searches=get(S/'searches.json')
 for r in searches:
  req(r['domain']==str(C.relative_to(R)),'fixed search domain')
  cp=subprocess.run(['rg','--no-ignore','-n','-i',r['pattern'],'.'],cwd=C,capture_output=True,text=True);req(cp.returncode in [0,1],'rg status')
  saved=get(S/'searches'/(r['label']+'.json'));req(len(saved)==r['lines'] and collections.Counter(saved)==collections.Counter(cp.stdout.splitlines()),'line multiset '+r['label'])
 passages=get(S/'passages.json');contracts=get(S/'read-contracts.json')
 for r in passages:
  lines=(R/r['path']).read_text().splitlines(keepends=True);text=''.join(lines[r['start']-1:r['end']])
  req(text==r['text'] and sha(text.encode())==r['sha256'],'actual passage')
 for r in contracts:
  req(sha((R/r['path']).read_bytes())==r['sha256'],'actual source contract hash')
  for a,b in r['ranges']:req(any(p['path']==r['path'] and p['start']==a and p['end']==b for p in passages),'contract coverage')
 primary=get(S/'primary/manifest.json');pdfs=0
 for r in primary:
  if 'path' not in r:req('error' in r,'retained request failure');continue
  req(sha((R/r['path']).read_bytes())==r['sha256'],'primary response')
  if 'text_path' in r:
   cp=subprocess.run(['pdftotext','-layout',str(R/r['path']),'-'],capture_output=True,check=True)
   req(cp.stdout==(R/r['text_path']).read_bytes() and sha(cp.stdout)==r['text_sha256'],'PDF replay '+r['name']);pdfs+=1
   if r.get('served_version'):req(r['served_version'] in cp.stdout.decode(),'served PDF version')
 for r in get(S/'primary-comparisons.json'):req(sha((R/r['current']).read_bytes())==sha((R/r['earlier']).read_bytes())==r['sha256'],'current primary text equality')
 for r in get(S/'raw-pin-comparisons.json'):req((R/r['response']).read_bytes()==(R/r['pin']).read_bytes() and blob((R/r['response']).read_bytes())==r['git_blob'],'fresh raw pin equality')
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
 author_bytes=subprocess.check_output([sys.executable,'frontier/experiments/i61_averaged_entropy_coefficient_rounding/verify.py'],cwd=R,env=env)
 author=json.loads(author_bytes);stored=get(E/'author-replay.json')
 req(author['status']=='PASS','unchanged author verifier PASS')
 for k,v in stored.items():
  if k!='mutable_ledger_drift':req(author[k]==v,'author replay '+k)
 diag_bytes=subprocess.check_output([sys.executable,str(E/'diagnostics.py')],cwd=R,env=env)
 req(diag_bytes==(E/'diagnostics.json').read_bytes(),'independent deterministic exact/floating replay')
 diag=json.loads(diag_bytes)
 return dict(status='PASS',sealed_artifacts=len(seal['artifacts']),inputs=len(inputs),mutable_ledger_drift=drift,tree_entries=len(tree),manuscripts=749,corpus_files=len(corpus),pins=len(pins),prior_files=len(prior),prior_brief_objection_copies=len(get(S/'prior-records.json')),search_line_multisets=[r['lines'] for r in searches],read_contracts=len(contracts),passages=len(passages),primary_responses=len(primary),successful_primary_responses=sum(r.get('status')==200 for r in primary),pdf_replays=pdfs,raw_pin_replays=len(get(S/'raw-pin-comparisons.json')),author_artifacts=author['artifacts'],author_exact_assertions=author['exact_assertions'],author_mutable_ledger_drift=author['mutable_ledger_drift'],independent_exact_assertions=diag['exact_assertions'],independent_floating_records=len(diag['floating_records']),limitation='Evidence and finite algebra replay only. Analytic verdict is in the I63 report. AR and U unproved and unrefuted; no contribution or count decision.')
if __name__=='__main__':
 try:print(json.dumps(main(),indent=2,sort_keys=True))
 except Exception as e:print(json.dumps(dict(status='FAIL',error=str(e)),indent=2));sys.exit(1)
