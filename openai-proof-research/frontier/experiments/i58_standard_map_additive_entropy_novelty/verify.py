#!/usr/bin/env python3
"""Read-only I58 integrity/replay verification; contribution reasoning is in the report."""
import collections,hashlib,json,pathlib,subprocess,sys
sys.dont_write_bytecode=True
R=pathlib.Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i58_standard_map_additive_entropy_novelty'
E=R/'frontier/experiments/i58_standard_map_additive_entropy_novelty'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
 b=p.read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def require(t,msg):
 if not t:raise AssertionError(msg)
def run(args):return subprocess.run(args,cwd=R,capture_output=True,text=True)
def main():
 seal=read(S/'seal.json')
 for x in seal['artifacts']:require(sha(R/x['path'])==x['sha256'],'own seal '+x['path'])
 mutable={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
 inputs=read(S/'inputs-manifest.json');drift=[]
 require({x['path'] for x in inputs if x['mutable_ledger']}==mutable,'exact four mutable ledgers')
 for x in inputs:
  require(sha(S/'inputs'/x['path'])==x['sha256'],'frozen input '+x['path'])
  if sha(R/x['path'])!=x['sha256']:
   require(x['path'] in mutable,'immutable live input '+x['path']);drift.append(x['path'])
 brief=read(S/'inputs/frontier/iterations/iteration58-standard-map-additive-entropy-novelty-task.json')['brief']
 require((S/'brief.txt').read_text()=='Act as the review sub-agent for this task.\n\n'+brief,'verbatim exact brief')
 tree=read(S/'inputs/sources/preprints-tree.json');require(not tree['truncated'] and len(tree['tree'])==13223,'complete tree')
 require(len({x['path'].split('/')[1] for x in tree['tree']})==749,'complete manuscript count')
 idx={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
 pins=read(S/'pinned-manifest.json')
 commit='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
 for x in pins:
  p=S/'pinned'/x['path'];require(sha(p)==x['sha256'] and blob(p)==x['blob']==idx[x['path']],'pin blob '+x['path'])
  require(x['url']==f'https://raw.githubusercontent.com/openai/math/{commit}/'+x['path'],'immutable pin URL')
 inv=read(S/'corpus-inventory.json');files=inv['files'];require(inv['manuscripts']==749 and len(files)==9340,'inventory dimensions')
 cor=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
 result=run(['rg','--files','--no-ignore',str(cor)]);require(result.returncode==0,'no-ignore inventory')
 require({str(pathlib.Path(x).relative_to(R)) for x in result.stdout.splitlines()}=={x['path'] for x in files},'all corpus files enumerated')
 for x in files:
  p=R/x['path'];require(sha(p)==x['sha256'] and blob(p)==x['blob']==idx[x['tree_path']],'corpus blob '+x['path'])
 passages=read(S/'passages.json')
 for x in passages:
  p=S/x['path'];require(sha(p)==x['sha256'],'passage file')
  part='\n'.join(p.read_text().split('\n')[x['start']-1:x['end']])+'\n'
  require(hashlib.sha256(part.encode()).hexdigest()==x['passage_sha256'],'passage range')
  for a in x['anchors']:require(a in part,'passage anchor '+a)
 contracts=read(S/'source-contracts.json')
 for x in contracts:
  require(sha(S/x['path'])==x['sha256'],'contract file')
  for a in x['labels']:require('\\label{'+a+'}' in (S/x['path']).read_text(),'contract label')
 responses=read(S/'responses.json')+read(S/'extra-responses.json')
 for x in responses:require(sha(S/x['path'])==x['sha256'],'response '+x['name'])
 for name in ['scales','bridge','geometry']:
  expected=next(x for x in pins if x['path'].endswith('/'+name+'.tex'))
  require(sha(S/'literature'/('pin-'+name+'.tex'))==expected['sha256'],'fresh pin '+name)
 pdfs=read(S/'pdf-extractions.json')+read(S/'extra-pdf-extractions.json')
 for x in pdfs:
  b=subprocess.check_output(['pdftotext','-layout',str(S/x['pdf']),'-']);require(hashlib.sha256(b).hexdigest()==x['sha256']==sha(S/x['text']),'PDF extraction')
 for x in read(S/'html-extractions.json'):require(sha(S/x['text'])==x['sha256'],'HTML readable hash')
 searches=read(S/'searches.json')
 for x in searches:
  result=run(x['args']);require(result.returncode in [0,1],'search exit')
  require(collections.Counter(result.stdout.splitlines())==collections.Counter(read(S/x['result'])),'search line multiset '+x['name'])
 prior={}
 for name in ['i52_ergodic_dynamical_discovery','i54_standard_map_additive_entropy','i57_standard_map_additive_entropy_r2']:
  old=read(S/'inputs/frontier/sources'/name/'seal.json');prior[name]=len(old['artifacts'])
  for x in old['artifacts']:require(sha(R/x['path'])==x['sha256'],'unchanged prior '+x['path'])
 # Preserve the failed vanilla I52 run, independently verify the exact growing-domain explanation.
 fail=read(S/'inputs/frontier/experiments/i57_standard_map_additive_entropy_r2/i52-direct-replay-failure.json')
 require(fail['exit_code']==1 and fail['failure']=='AssertionError: search multiset prior-screens','retained direct failure')
 old=collections.Counter(read(S/'inputs/frontier/sources/i57_standard_map_additive_entropy_r2/i52-prior-screens-original.json'))
 current=run(fail['historical_search_args']);require(current.returncode in [0,1],'historical search execution')
 new=collections.Counter(current.stdout.splitlines())
 require(not old-new and new-old==collections.Counter(fail['added']),'exact historical additions, no removals')
 require(sum((new-old).values())==12 and {x.split(':')[0] for x in new-old}=={'frontier/iterations/i54-standard-map-additive-entropy.md'},'12 later I54 lines only')
 require(new==collections.Counter(read(S/'inputs/frontier/sources/i57_standard_map_additive_entropy_r2/i52-prior-screens-current.json')),'retained current historical multiset')
 diag=run([sys.executable,'-B',str(E/'diagnostics.py')]);require(diag.returncode==0,'own diagnostics execute')
 d=json.loads(diag.stdout);require(d==read(E/'diagnostics.json'),'own diagnostic replay')
 i52=run([sys.executable,'-B','frontier/experiments/i52_ergodic_dynamical_discovery/diagnostics.py']);require(i52.returncode==0,'separate I52 diagnostics execute')
 require(json.loads(i52.stdout)==read(S/'inputs/frontier/experiments/i52_ergodic_dynamical_discovery/diagnostics.json'),'I52 separate diagnostics exactly match')
 for name in ['i54','i57']:
  require(read(E/(name+'-replay.json'))['status']=='PASS','retained successful '+name+' read-only replay')
 for x in seal['artifacts']:require(sha(R/x['path'])==x['sha256'],'own post-check seal')
 print(json.dumps({'status':'PASS','read_only':True,'scope':'Integrity and finite diagnostics; contribution decision and mathematical reduction are in I58 report; I57 owns full original-proof PASS','sealed_artifacts':len(seal['artifacts']),'inputs':len(inputs),'live_mutable_ledger_drift':drift,'pins':len(pins),'contracts':len(contracts),'passages':len(passages),'tree_entries':13223,'manuscripts':749,'corpus_files':len(files),'search_line_multisets':{x['name']:x['lines'] for x in searches},'fresh_primary_responses':len(responses),'http_successes':sum(x['status']==200 for x in responses),'http_failures':[x for x in responses if x['status']!=200],'pdf_reextractions':len(pdfs),'prior_sealed_artifacts_unchanged':prior,'I54_retained_original_replay':'PASS','I57_retained_original_replay':'PASS','I52_vanilla_verifier':'FAIL retained; historical search gained exactly 12 later I54 matches, no removals','I52_separate_finite_assertions':json.loads(i52.stdout)['assertions'],'independent_exact_assertions':d['assertions'],'floating_trajectories':0},indent=2,sort_keys=True))
if __name__=='__main__':main()
