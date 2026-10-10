"""Offline sealed R3 verification. Never refreshes author, R2, or R3 seals."""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[3];E=Path(__file__).resolve().parent;S=R/'frontier/sources/i38_propeller_stability_novelty_r3'
sys.path.insert(0,str(E))
import check,search_corpus,reproduce_prior
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 errors=[];drift=[];counts={}
 try:
  seal=json.loads((S/'artifact-seal.json').read_text())
  for x in seal['files']:assert sha(R/x['path'])==x['sha256'],x['path']
  counts['sealed_artifacts']=len(seal['files'])
  inputs=json.loads((S/'input-manifest.json').read_text())
  for x in inputs:
   assert sha(R/x['frozen'])==x['sha256'],x['frozen']
   now=sha(R/x['path'])
   if now!=x['sha256']:
    if x['mutable']:drift.append({'path':x['path'],'frozen':x['sha256'],'live':now})
    else:raise AssertionError('immutable dependency drift: '+x['path'])
  counts['frozen_inputs']=len(inputs)
  rows=json.loads((S/'selected-pinned.json').read_text());tree={x['path']:x for x in json.loads((R/'sources/preprints-tree.json').read_text())['tree']}
  for x in rows:
   p=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'/x['path'];b=p.read_bytes()
   assert sha(p)==x['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==tree[x['path']]['sha']
   assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
  counts['selected_pinned']=len(rows)
  manifests=['manifest.json','followup-manifest.json','additional-manifest.json'];primary=[]
  for name in manifests:primary+=json.loads((S/'literature'/name).read_text())
  for x in primary:
   p=S/'literature'/x['name'];assert sha(p)==x['sha256'];assert p.stat().st_size==x['bytes']
   if x['name'].endswith('.pdf') and x['status']==200:assert p.read_bytes().startswith(b'%PDF')
  counts['primary_responses']=len(primary);counts['retained_failed_responses']=sum(x['status']!=200 for x in primary)
  reads=json.loads((S/'read-log.json').read_text())
  for x in reads:
   p=R/x['path'];assert sha(p)==x['sha256'];a=p.read_bytes().splitlines(keepends=True);assert hashlib.sha256(b''.join(a[x['start']-1:x['end']])).hexdigest()==x['passage_sha256']
  for x in json.loads((S/'manual-read-scope.json').read_text()):assert sha(R/x['path'])==x['sha256']
  counts['opened_passages']=len(reads)
  corpus,_=search_corpus.run();assert corpus==json.loads((S/'corpus-search.json').read_text())
  counts.update(corpus_files=corpus['files'],corpus_bytes=corpus['bytes'],inventory_entries=corpus['tree_entries'],manuscripts=corpus['manuscripts'])
  checks=check.run();assert checks==json.loads((E/'checks.json').read_text());counts['exact_finite_checks']=checks['exact_finite_checks']
  prior=reproduce_prior.run();counts['unchanged_prior_files']=prior['unchanged_prior_files']
  # Re-check our own seal after executing imported prior verifiers.
  for x in seal['files']:assert sha(R/x['path'])==x['sha256'],x['path']
 except Exception as exc:
  errors.append(repr(exc));prior=None
 out={'status':'PASS' if not errors else 'FAIL','counts':counts,'mutable_shared_ledger_drift':drift,'immutable_dependency_errors':errors,'prior_reproduction':prior,'scope':'Integrity and deterministic reproduction, not an analytic-proof or priority certificate.'}
 (E/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items() if k!='prior_reproduction'},indent=2));return bool(errors)
if __name__=='__main__':raise SystemExit(main())
