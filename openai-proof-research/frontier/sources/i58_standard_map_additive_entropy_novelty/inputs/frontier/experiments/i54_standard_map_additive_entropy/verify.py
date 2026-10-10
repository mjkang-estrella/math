#!/usr/bin/env python3
"""Read-only provenance and finite algebra; not analytic proof certification."""
import collections,hashlib,json,pathlib,subprocess,sys
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[3]
SRC=ROOT/'frontier/sources/i54_standard_map_additive_entropy'
EXP=ROOT/'frontier/experiments/i54_standard_map_additive_entropy'
COR=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
 b=p.read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def req(x,msg):
 if not x:raise AssertionError(msg)
def main():
 seal=read(SRC/'seal.json')
 for r in seal['artifacts']:req(sha(ROOT/r['path'])==r['sha256'],'I54 artifact '+r['path'])
 inputs=read(SRC/'inputs-manifest.json');drift=[]
 for r in inputs:
  req(sha(SRC/'inputs'/r['path'])==r['sha256'],'frozen input '+r['path'])
  if sha(ROOT/r['path'])!=r['sha256']:
   if r['mutable_ledger']:drift.append(r['path'])
   else:raise AssertionError('immutable input drift '+r['path'])
 brief=read(SRC/'inputs/frontier/iterations/iteration54-standard-map-additive-entropy-task.json')['brief']
 req((SRC/'brief.txt').read_text()=='Act as the research sub-agent for this task.\n\n'+brief,'verbatim brief')
 prior=read(SRC/'inputs/frontier/sources/i52_ergodic_dynamical_discovery/seal.json')
 for r in prior['artifacts']:req(sha(ROOT/r['path'])==r['sha256'],'immutable I52 artifact '+r['path'])
 tree=read(SRC/'inputs/sources/preprints-tree.json')
 req(not tree['truncated'] and len(tree['tree'])==13223,'full tree')
 names={r['path'].split('/')[1] for r in tree['tree'] if r['path'].count('/')>=2}
 req(len(names)==749,'manuscript count')
 index={r['path']:r for r in tree['tree'] if r['type']=='blob'}
 pin=read(SRC/'pinned-manifest.json')
 for r in pin:
  p=SRC/'pinned'/r['path'];req(sha(p)==r['sha256'],'pin sha');req(blob(p)==r['blob']==index[r['path']]['sha'],'pin blob')
 inv=read(SRC/'corpus-inventory.json')
 live=subprocess.check_output(['rg','--files','--no-ignore',str(COR)],cwd=ROOT,text=True).splitlines()
 req(len(inv)==9340,'corpus size')
 req({str(pathlib.Path(p).relative_to(COR)) for p in live}=={r['path'] for r in inv},'corpus inventory')
 for r in inv:
  p=COR/r['path'];req(sha(p)==r['sha256'] and blob(p)==r['blob']==index[r['path']]['sha'],'corpus '+r['path'])
 passages=read(SRC/'passages.json')
 for r in passages:
  p=SRC/r['path'];req(sha(p)==r['sha256'],'passage source')
  lines=p.read_text().splitlines();s='\n'.join(lines[r['start']-1:r['end']])+'\n'
  req(hashlib.sha256(s.encode()).hexdigest()==r['passage_sha256'],'passage range')
  for a in r['anchors']:req(a in s,'anchor '+a)
 contracts=read(SRC/'source-contracts.json')
 for r in contracts:
  p=SRC/r['path'];req(sha(p)==r['sha256'],'contract source')
  for a in r['labels']:req('\\label{'+a+'}' in p.read_text(),'contract label '+a)
 responses=read(SRC/'responses.json')
 for r in responses:
  if 'path' in r:req(sha(SRC/r['path'])==r['sha256'],'response '+r['name'])
 manuscript='Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026'
 for part in ['bridge','geometry']:
  req((SRC/'literature'/('pin-'+part+'.tex')).read_bytes()==(SRC/'pinned/preprints'/manuscript/'build/sections'/(part+'.tex')).read_bytes(),'fresh pinned '+part)
 extractions=read(SRC/'pdf-extractions.json')
 for r in extractions:
  b=subprocess.check_output(['pdftotext','-layout',str(SRC/r['pdf']),'-'])
  req(hashlib.sha256(b).hexdigest()==r['text_sha256']==sha(SRC/r['text']),'pdf replay '+r['pdf'])
 searches=read(SRC/'searches.json')
 for r in searches:
  z=subprocess.run(r['args'],cwd=ROOT,capture_output=True,text=True)
  req(z.returncode in (0,1),'rg execution')
  req(collections.Counter(z.stdout.splitlines())==collections.Counter(read(SRC/r['result'])),'rg multiset '+r['name'])
 diag=json.loads(subprocess.check_output([sys.executable,'-B',str(EXP/'diagnostics.py')],cwd=ROOT,text=True))
 req(diag==read(EXP/'diagnostics.json'),'finite diagnostic replay')
 for r in seal['artifacts']:req(sha(ROOT/r['path'])==r['sha256'],'post-replay I54 artifact')
 print(json.dumps({'status':'PASS','scope':'provenance and finite algebra, not analytic proof or novelty certification','read_only':True,'sealed_artifacts':len(seal['artifacts']),'unchanged_I52_artifacts':len(prior['artifacts']),'frozen_inputs':len(inputs),'live_mutable_ledger_drift':drift,'pinned_files':len(pin),'pinned_manuscripts':1,'complete_tree_entries':13223,'complete_manuscripts':749,'corpus_files':len(inv),'source_contracts':len(contracts),'passages':len(passages),'fresh_http_responses':len(responses),'http_successes':sum(r.get('status')==200 for r in responses),'http_failures':[r for r in responses if r.get('status')!=200],'pdf_reextractions':len(extractions),'search_multisets':{r['name']:r['lines'] for r in searches},'exact_finite_assertions':diag['exact_assertions'],'floating_diagnostic_rows':len(diag['floating_diagnostics']['rows']),'floating_diagnostic_scope':diag['floating_diagnostics']['kind']},indent=2,sort_keys=True))
if __name__=='__main__':main()
