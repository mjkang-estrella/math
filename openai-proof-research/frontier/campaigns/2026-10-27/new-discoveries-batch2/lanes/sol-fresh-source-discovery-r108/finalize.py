from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).parent;R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');B=L.parent.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b)
 return h.hexdigest()
g=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';assert sha(g)=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
ctx=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'NEXT.md',B/'prior-campaign-context.json',L.parent/'sol-fresh-source-discovery-r105/SUMMARY.md',L.parent/'sol-fresh-source-discovery-r105/provenance.json']
(L/'context-hashes.json').write_text(json.dumps([{'path':str(p),'sha256':sha(p)} for p in ctx],indent=2))
sources=[{'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted((L/'sources').iterdir()) if p.is_file()]
(L/'sourcebytes.sha256').write_text(''.join(x['sha256']+'  '+x['path']+'\n' for x in sources))
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'ZERO_ELIGIBLE_SURVIVORS','credit':0,'counts':{'additional':8,'total':38},'primary':'https://arxiv.org/html/2610.29846v1','targets':[{'label':'Section7 item5','scope':'full separator classification for j>m','status':'UNRESOLVED'},{'label':'Section7 item6','scope':'all m>2,K>2m,j>=1; explicit representatives with double-factorial counts','ordinary_math':'FULL_PROOF','status':'EXCLUDED_ROUTINE_SOURCE_ADAPTATION','proof':'PROOF.md','source_subsumer':'Proposition5.24 tree-counting mechanism'},{'label':'Section7 item8','scope':'universal five-occurrence cutoff for packing sequences','status':'UNRESOLVED'}],'Lean':False,'paper':False,'sources':sources,'duplicate_screen':json.loads((L/'duplicate-summary.json').read_text()),'registry':{'omega_HEAD':'89cda9c274d1122b7676173296af3047c3b64cd1','omega_author_utc':'2026-10-29T20:10:57Z','omega_committer_utc':'2026-10-29T20:10:57Z','openai_HEAD':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','comparison_base':'73a5033dd654a16a14fcd1b13277f1a03d81d826','delta_commits':7,'delta_paths':3,'recursive_tree_retried':False,'global_semantic_clearance':False,'limits':'Inherited18:13complete baseline/short-chain only; old aggregate300cap and r105403 remain explicit; commit times do not date every theorem'},'checks':json.loads((L/'check-results.json').read_text()),'uniform_checks':{'pairs':16,'j_max':9},'verification':json.loads((L/'verification.json').read_text()),'helper_policy':{'guard':str(g),'sha256':sha(g),'AS_groupRSS_MiB':512,'CPU_s':210,'wall_s':230,'nominal_sample_ms':40,'BLAS_threads':1,'raised_caps':False,'unguarded_python_helpers':False},'failures':['latest Sahbi HTML404','Sahbi v4 HTML404'],'strongest_objection':'The sole full ordinary answer is a routine same-source tree formula adaptation; no eligible discovery survives.','precise_gaps':{'item5':'all-pattern/all-j separator classification','item6':'no ordinary math gap; substantive eligibility fails and priority unestablished','item8':'uniform all-pattern state reconstruction or actual source-compatible pair splitting after five'},'manifest_excludes':['manifest.sha256'],'no_shared_writes':True}
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
with (L/'manifest.sha256').open('w') as f:
 for p in sorted(L.rglob('*')):
  if p.is_file() and p.name!='manifest.sha256':f.write(sha(p)+'  '+str(p.relative_to(L))+'\n')
print('FINALIZED',len(sources),'source files; credit0')
