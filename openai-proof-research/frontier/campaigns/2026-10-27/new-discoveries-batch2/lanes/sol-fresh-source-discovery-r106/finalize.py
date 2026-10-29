from pathlib import Path
import hashlib,json,datetime
P=Path(__file__).resolve().parent;R=Path('openai-proof-research').resolve();B=P.parent.parent

def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  for b in iter(lambda:s.read(65536),b''):h.update(b)
 return h.hexdigest()
ctx=[R/'AGENTS.md',B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md',P.parent/'sol-fresh-source-discovery-r103/SUMMARY.md',P.parent/'sol-fresh-source-discovery-r103/discovery.md',P.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']
context={str(f):sha(f) for f in ctx}
# Read full JSON context bodies without aggregating unrelated files.
ledger=json.loads((B/'ledger.json').read_text());prior=json.loads((B/'prior-campaign-context.json').read_text())
audit=json.loads((P/'duplicate-audit.json').read_text());checks=json.loads((P/'check-results.json').read_text())
assert ledger['accepted_count']==8 and ledger['total_accepted_count']==38
raw=[]
for name in ['http.json','more-http.json']:
 for row in json.loads((P/name).read_text()):
  if row.get('status')==200:
   f=P/row['file'];assert sha(f)==row['sha256'];raw.append(row)
(P/'sourcebytes.sha256').write_text(''.join(f"{r['sha256']}  {r['file']}\n" for r in raw))
base={}
for name in ['omega','openai']:
 f=P.parent/'root-edge-irregulator-final-freeze-r1'/f'{name}-tree.txt';base[name]={'path':str(f),'sha256':sha(f),'scope':'Inherited complete18:13baseline path inventory; no semantic/current-head clearance.'}
out={'lane':str(P),'finalized_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED','credit':0,'counts':{'additional':8,'total':38},'primary':'https://arxiv.org/abs/2605.02023v1','selected_statements':['Conjecture3.1 full Gaussian-minimum stochastic domination','Conjecture4.1 all-dimensional zone-union measure comparison'],'families':1,'context_read_sha256':context,'context_json_read':{'ledger_accepted':len(ledger.get('accepted',[])),'prior_accepted':len(prior.get('accepted',[]))},'duplicate_screen':{'files':audit['files'],'errors':audit['errors'],'literal_id_selfcheck':audit['literal_id_selfcheck'],'inventory':'duplicate-corpus.jsonl','patterns_and_hits':'duplicate-audit.json'},'registry':{'live_head_refresh':'Both403 rate-limit exceeded; no retries; current-head HOLD','last_supplied_omega':'73a5033dd654a16a14fcd1b13277f1a03d81d826','last_supplied_openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','baseline':base,'actual_bodies':['sources/registry-softminimum.lean','sources/registry-cdso.md'],'coverage':'Large aggregate300-file cap and baseline-to-shortchain semantic gap retained; no absence grep or merge-date priority inference'},'sources':raw,'access_failures':'failures.md and HTTP receipts','checks':checks,'strongest_objection':'No measure-preserving/monotone planarization for higher-rank zones; covering existence does not bound uncovered measure. Interpolation failure is not source refutation.','precise_gap':'Universal higher-rank/all-threshold comparison, or actual admissible rigorously bounded counterexample; latest registry and local-stability successor semantic gaps.','guard':{'path':str(ctx[-1]),'sha256':sha(ctx[-1]),'AS_and_groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'BLAS_threads':1,'raised_caps':False},'no_PROOF_md':not(P/'PROOF.md').exists(),'writes':'Own lane only; no children/git/shared writes/browser/accounts/contacts/post/upload'}
(P/'provenance.json').write_text(json.dumps(out,indent=2))
files=sorted(f for f in P.rglob('*') if f.is_file() and f.name!='manifest.sha256')
(P/'manifest.sha256').write_text(''.join(f'{sha(f)}  {f.relative_to(P)}\n' for f in files))
print(json.dumps({'status':out['status'],'credit':0,'manifest_files':len(files),'source_bytes_files':len(raw),'corpus_files':audit['files'],'counts':out['counts']}))
