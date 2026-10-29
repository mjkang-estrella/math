import json,hashlib,gzip,time
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5];B=L.parent.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while c:=f.read(65536):h.update(c)
 return h.hexdigest()
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
more=[B/'lanes'/p for p in ['sol-renyi-registry-gap-closure-r3/review.md','sol-factorial-product-prior-clearance-r2/review.md','sol-fresh-source-discovery-r51/SUMMARY.md','sol-fresh-source-discovery-r51/discovery.md','sol-fresh-source-discovery-r51/progress.md','root-fresh-source-r51-handback/ADOPTION.json','root-real-mathieu-exclusion-r1/EXCLUSION.json']]
more.extend(R/p for p in ['frontier/campaigns/2026-10-26/new-discoveries/lanes/parent-analysis-screen-r7/STATUS.md'])
rec=[]
for i,p in enumerate(more):
 dest=L/'sources'/('history-%02d'%i+p.suffix);dest.write_bytes(p.read_bytes());rec.append({'original':str(p),'copy':str(dest.relative_to(L)),'sha256':sha(dest)})
dump('additional-context-receipts.json',rec)
targethashes={json.loads(s)['sha256'] for s in (L/'target-matches.jsonl').open()};aliases=[]
with gzip.open(L/'pathmap.jsonl.gz','rt') as f:
 for s in f:
  h,p=json.loads(s)
  if h in targethashes and 'new-discoveries-batch2/lanes/' in p and Path(p).name.lower() in {'summary.md','discovery.md','review.md','decision.md','exclusion.json','adoption.json','status.md'}:
   aliases.append({'sha256':h,'path':p})
dump('target-report-aliases.json',aliases)
next_now=sha(B/'NEXT.md');next_asread=sha(L/'sources/context-04.md')
guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
dump('source-lock.json',[{'path':str(p.relative_to(L)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted((L/'sources').iterdir()) if p.is_file()])
dump('provenance.json',{'lane':str(L),'utc_completed':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'disposition':'NO_ELIGIBLE_NOMINATION','full_eligible_candidate':False,'PROOF_md':False,'helper_guard':{'path':str(guard),'sha256':sha(guard),'unchanged_expected':'825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45','AS_and_groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'sampling_ms':40,'BLAS_threads':1},'context':{'as_read_receipts':'context-receipts.json','additional_receipts':'additional-context-receipts.json','NEXT_as_read_sha256':next_asread,'NEXT_final_observed_sha256':next_now,'NEXT_is_scientific_freeze':False,'mutable_next_changed':next_now!=next_asread},'research':{'all_date_stream':'screen-receipt.json','path_hash_mapping':'pathmap.jsonl.gz','deduplicated_representatives':'screen.sqlite','second_target_stream':'target-scan-receipt.json','recent_report_aliases':'target-report-aliases.json','bounded_reads':'discovery.md','source_receipts':'http.jsonl','source_lock':'source-lock.json'},'registry':{'fresh_requests':0,'reason':'No meaningful eligible survivor; no target-specific novelty clearance claimed','reused_fixed_Omega_heads':['d254db264d94f6837888d045d5c12126faa84a5c','c3e8754b8890ac2c4da1d45d41cf530fac36d85d'],'OpenAI_inherited_head':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','scope_limit':'Selective historical baseline and complete bounded first-parent/mainline terminal states; not every sidebranch transient or all-body semantics'},'access_failures':[{'url':'https://doi.org/10.13140/RG.2.2.22499.94241','status':403,'bypass':False}],'external_mutations':False,'children':False,'shared_edits':False,'git_operations':False,'Lean_or_manuscript':False,'checks':'checks.json','honesty':'Problem1 exact source question already screened r51; all-order route routine. Problems2/3 public proofs. No full fresh substantive result.'})
assert sha(guard)=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
# Manifest and verifier exclude each other, avoiding circular self-hashing.
excluded={'finalmanifest.json','manifest-verification.json'}
files={str(p.relative_to(L)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}
dump('finalmanifest.json',{'files':files,'excluded':sorted(excluded),'scope':'All delivered lane files; context copies frozen as read, not assertions that originals remain unchanged.'})
fail=[]
for name,r in files.items():
 if sha(L/name)!=r['sha256']:fail.append(name)
dump('manifest-verification.json',{'status':'PASS' if not fail else 'FAIL','checked':len(files),'failures':fail,'manifest_sha256':sha(L/'finalmanifest.json'),'source_lock_count':len(json.loads((L/'source-lock.json').read_text())),'no_PROOF_md':not (L/'PROOF.md').exists(),'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})
print(json.dumps({'manifest_entries':len(files),'failures':fail,'target_report_aliases':len(aliases),'NEXT_changed':next_now!=next_asread}))
assert not fail
