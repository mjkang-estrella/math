#!/usr/bin/env python3
"""Read-only evidence verification; analytic conclusions are in the I57 review."""
import collections,hashlib,json,pathlib,subprocess,sys
sys.dont_write_bytecode=True
R=pathlib.Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i57_standard_map_additive_entropy_r2'
E=R/'frontier/experiments/i57_standard_map_additive_entropy_r2'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
 b=p.read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def req(x,m):
 if not x:raise AssertionError(m)
def run(args):
 return subprocess.run(args,cwd=R,text=True,capture_output=True)
def main():
 seal=read(S/'seal.json')
 for x in seal['artifacts']:req(sha(R/x['path'])==x['sha256'],'I57 sealed '+x['path'])
 drift=[];inputs=read(S/'inputs-manifest.json')
 for x in inputs:
  req(sha(S/'inputs'/x['path'])==x['sha256'],'frozen '+x['path'])
  if sha(R/x['path'])!=x['sha256']:
   req(x['mutable_ledger'],'immutable live drift '+x['path']);drift.append(x['path'])
 task=read(S/'inputs/frontier/iterations/iteration57-standard-map-additive-entropy-r2-task.json')
 req((S/'brief.txt').read_text()=='Act as the review sub-agent for this task.\n\n'+task['brief'],'verbatim review brief')
 prior={}
 for name in ['i52_ergodic_dynamical_discovery','i54_standard_map_additive_entropy']:
  p=read(S/'inputs/frontier/sources'/name/'seal.json')
  for x in p['artifacts']:req(sha(R/x['path'])==x['sha256'],'prior seal '+x['path'])
  prior[name]=len(p['artifacts'])
 tree=read(S/'inputs/sources/preprints-tree.json')
 req(len(tree['tree'])==13223 and not tree['truncated'],'complete tree')
 req(len({x['path'].split('/')[1] for x in tree['tree'] if x['path'].count('/')>=2})==749,'manuscripts')
 idx={x['path']:x for x in tree['tree'] if x['type']=='blob'}
 pins=read(S/'pinned-manifest.json')
 for x in pins:
  p=S/'pinned'/x['path'];req(sha(p)==x['sha256'],'pin sha');req(blob(p)==x['blob']==idx[x['path']]['sha'],'pin Git blob')
 inv=read(S/'inputs/frontier/sources/i54_standard_map_additive_entropy/corpus-inventory.json')
 cor=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
 z=run(['rg','--files','--no-ignore',str(cor)]);req(z.returncode==0,'corpus inventory command')
 req(len(inv)==9340 and {str(pathlib.Path(p).relative_to(cor)) for p in z.stdout.splitlines()}=={x['path'] for x in inv},'corpus inventory')
 for x in inv:
  p=cor/x['path'];req(sha(p)==x['sha256'] and blob(p)==x['blob']==idx[x['path']]['sha'],'corpus blob '+x['path'])
 passages=read(S/'passages.json')
 for x in passages:
  p=S/x['path'];req(sha(p)==x['sha256'],'passage file');lines=p.read_text().splitlines();b=('\n'.join(lines[x['start']-1:x['end']])+'\n').encode();req(hashlib.sha256(b).hexdigest()==x['passage_sha256'],'passage range')
 contracts=read(S/'source-contracts.json')
 for x in contracts:
  p=S/x['path'];req(sha(p)==x['sha256'],'contract file')
  for anchor in x['labels']:req('\\label{'+anchor+'}' in p.read_text(),'contract label '+anchor)
 searches=read(S/'searches.json')
 for x in searches:
  z=run(x['args']);req(z.returncode in (0,1),'search execution')
  req(collections.Counter(z.stdout.splitlines())==collections.Counter(read(S/x['result'])),'I57 search multiset '+x['name'])
 # Keep direct prior failure visible. Check its exact explanation, not a patched PASS.
 fail=read(E/'i52-direct-replay-failure.json')
 req(fail['exit_code']==1 and fail['failure']=='AssertionError: search multiset prior-screens','retained failure')
 old=collections.Counter(read(S/'i52-prior-screens-original.json'));cur=run(fail['historical_search_args']);req(cur.returncode in (0,1),'prior search execution')
 new=collections.Counter(cur.stdout.splitlines())
 req(old==collections.Counter(read(S/'inputs/frontier/sources/i52_ergodic_dynamical_discovery/prior-screens-search.json')),'original prior snapshot')
 req(new==collections.Counter(read(S/'i52-prior-screens-current.json')),'current prior snapshot')
 req(not old-new and new-old==collections.Counter(fail['added']),'exact historical-domain delta')
 req(len(list((new-old).elements()))==12 and {x.split(':')[0] for x in (new-old)}=={'frontier/iterations/i54-standard-map-additive-entropy.md'},'delta only later I54')
 for x in read(S/'responses.json'):
  req(sha(S/x['path'])==x['sha256'],'retained response body')
 extractions=read(S/'pdf-extractions.json')
 for x in extractions:
  b=subprocess.check_output(['pdftotext','-layout',str(S/x['pdf']),'-'])
  req(hashlib.sha256(b).hexdigest()==x['text_sha256']==sha(S/x['text']),'PDF replay')
 diag=run([sys.executable,'-B',str(E/'diagnostics.py')]);req(diag.returncode==0,'I57 diagnostic execution')
 d=json.loads(diag.stdout);req(d==read(E/'diagnostics.json'),'I57 diagnostic output')
 prior_diag=run([sys.executable,'-B','frontier/experiments/i52_ergodic_dynamical_discovery/diagnostics.py'])
 req(prior_diag.returncode==0 and json.loads(prior_diag.stdout)==read(S/'inputs/frontier/experiments/i52_ergodic_dynamical_discovery/diagnostics.json'),'separate I52 diagnostic replay')
 replay=run([sys.executable,'-B','frontier/experiments/i54_standard_map_additive_entropy/verify.py'])
 req(replay.returncode==0,'I54 unchanged verifier replay '+replay.stderr)
 i54=json.loads(replay.stdout);req(i54['status']=='PASS','I54 replay status')
 for x in seal['artifacts']:req(sha(R/x['path'])==x['sha256'],'post-check I57 '+x['path'])
 for name in prior:
  for x in read(S/'inputs/frontier/sources'/name/'seal.json')['artifacts']:req(sha(R/x['path'])==x['sha256'],'post-check prior '+x['path'])
 print(json.dumps({'status':'PASS','scope':'Read-only provenance and finite diagnostics; analytic verdict is in the review','sealed_artifacts':len(seal['artifacts']),'frozen_inputs':len(inputs),'live_mutable_ledger_drift':drift,'prior_artifacts_unchanged':prior,'complete_tree_entries':13223,'complete_manuscripts':749,'corpus_files':len(inv),'pinned_files':len(pins),'full_or_primary_passages':len(passages),'source_contracts':len(contracts),'search_multisets':{x['name']:x['lines'] for x in searches},'I54_original_verifier':'PASS','I54_historical_ledger_drift':i54['live_mutable_ledger_drift'],'I52_original_verifier':'FAIL retained: historical prior-screens domain grew by 12 I54 matches; no removals','I52_separate_diagnostic_assertions':json.loads(prior_diag.stdout)['assertions'],'new_primary_version_responses':len(read(S/'responses.json')),'pdf_reextractions':len(extractions),'independent_exact_assertions':d['exact_assertions'],'synthetic_rational_rows':len(d['synthetic_rational_deficit_rows']),'read_only':True},indent=2,sort_keys=True))
if __name__=='__main__':main()
