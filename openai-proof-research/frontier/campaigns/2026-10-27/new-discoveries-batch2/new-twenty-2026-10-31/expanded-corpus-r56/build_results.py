from pathlib import Path
import hashlib,json,datetime,subprocess
w=Path(__file__).resolve().parent;e=json.loads((w/'extracted.json').read_text());r=json.loads((w/'reservation.json').read_text());out={}
notes={
361591:('excluded_same_source_theorem','Theorem 1.8 already resolves exact conjecture; d-rigidity gives d-connectivity and is retained after deleting the disjoint tree.','theorem statements and selected proof passages', '2401.12670'),
361623:('excluded_routine_conditional_source_consequence','Theorem 7 plus antecedent substitution is exactly Conjecture 8.','Theorem 7 full short proof and Conjecture 8', '2401.14768'),
361679:('source_corollary_significance_objection_zero_credit','Full ordinary weighted-zero-sum join argument in MATHEMATICS.md. Direct same-source Proposition 4.12/Lemma 4.13 bridge; no independent qualification or literal Lean.','address/language definitions, Proposition 4.11/4.12 proofs, Lemma 4.13 proof and exact conjecture','2402.00237'),
361793:('parked_old_example_bridge_and_normalization_gap','Classical resistance-three example obstructs factor-two version via r<=2er. Predecessor normalization body unread after 403; no candidate promoted.','exact Conjecture 16 definitions, Corollary 17 proof; older 1212.3641 Section 7 construction/proof','2402.06008'),
362246:('unresolved_sustained_exact_cover_attempt','a=6,c=5 positive partition checked; c=7 timeout; no uniform construction or certified negative witness. Parameter instance earns no credit.','Definition 10.1/Conjecture 10.2, tilted-order/rank definitions, small-case construction/proof discussion','2403.06318')}
fetchonly={361860:'2402.09254',361861:'2402.09254',361862:'2402.09254',362059:'2402.17413',362102:'2402.18955',362103:'2402.18955'}
for i,x in e.items():
 d=x['record'];n=int(i);z={k:v for k,v in x.items() if k!='record'};z.update(mathdb_id=n,title=d['title'],literal_statement=d['statement'],statement_sha256=hashlib.sha256(d['statement'].encode()).hexdigest(),raw_file='raw/'+i+'.jsonl',source_url=d['source_url'],canonical_url=d['canonical_url'],accepted_credit=0,statement_read=True,primary_body_review=False,proof_endpoint=None,inherited_matches=[],historical_search='history-matches.json; report-file bounded ID/title search, not global technical nonreview',novelty_status='not cleared',remaining_lemmas=[],outcome='unresolved_statement_screen_only',reason='Exact literal statement read. No source-body theorem/proof review or full-scope tractable mechanism completed; no exclusion/novelty assertion.')
 if n in notes:
  status,reason,depth,a=notes[n];z.update(outcome=status,reason=reason,primary_body_review=True,actual_review_depth=depth,source_receipts=['sources/'+a+'.receipt.json'],mathematics='MATHEMATICS.md')
 else:z['actual_review_depth']='literal record only; primary definitions not recovered'
 if n in fetchonly:
  z.update(actual_review_depth='literal statement; source PDF retrieved, relevant definitions/theorem/proof bodies NOT reviewed',source_receipts=['sources/'+fetchonly[n]+'.receipt.json'])
 if n==361793:z['source_receipts']+=['sources/1212.3641.receipt.json','sources/allie-publisher.receipt.json'];z['remaining_lemmas']=['Authenticate Allie predecessor definitions and scaling; routine-bridge objection already prevents new discovery investment.']
 if n==361679:z['remaining_lemmas']=['Qualification: independently adjudicate routine source-corollary objection.','If reopened, formalize actual top-address language and prove weighted-sum characterization from its definitions; finite weighted checker alone is not a literal Lean endpoint.']
 if n==362246:z['remaining_lemmas']=['Uniform ribbon decomposition for arbitrary a and coprime c, or exact source-valid obstruction.'];z['diagnostics']=['ribbon_scan.py','ribbon_pruned.py','ribbon-output.json','ribbon-pruned-output.json']
 if n==361679:z['diagnostics']=['banned_scan.py','banned-output.json']
 out[i]=z
(w/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
# Bind reservation inputs and corpus manifest, without silently trusting the hashes.
audit=[]
for f,h in r['input_hashes'].items():
 b=Path(f).read_bytes();got=hashlib.sha256(b).hexdigest();audit.append(dict(path=f,expected=h,actual=got,matches=got==h,mutable_context=f.endswith('ledger.json')))
base=w.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301';m=json.loads((base/'manifest.json').read_text());chunks=[]
for f in m['files']:
 if f['path'].startswith('corpus/mathdb-normalized-chunk-'):
  got=hashlib.sha256((base/f['path']).read_bytes()).hexdigest();chunks.append(dict(path=f['path'],expected=f['sha256'],actual=got,matches=got==f['sha256']))
(w/'input-verification.json').write_text(json.dumps(dict(reservation_inputs=audit,corpus_chunks=chunks),indent=2))
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean');manifest=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json');env=dict(lean_binary=str(lean),lean_binary_sha256=hashlib.sha256(lean.read_bytes()).hexdigest(),lean_version=subprocess.run([str(lean),'--version'],capture_output=True,text=True).stdout.strip(),lake_manifest=str(manifest),lake_manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),mathlib_rev=json.loads(manifest.read_text())['packages'][0]['rev'],formal_compilation_performed=False,trust='No Lean theorem packet. Cached upstream oleans not rebuilt or audited; no upstream trust claim.',limits='Expensive runs pinned to CPUs 0,1; address-space cap 6 GiB bounds RSS from above; CPU<=120 seconds and wall<=140 seconds per process. HiGHS threads=2; OMP<=2 and BLAS=1. No full aggregate/transient RSS telemetry.')
(w/'environment.json').write_text(json.dumps(env,indent=2))
assert len(out)==40 and set(map(int,out))==set(r['ids'])
print('exact 40 IDs; all zero credit; manifest chunks',len(chunks),'verified',all(x['matches'] for x in chunks));print('reservation inputs',[(x['path'].split('/')[-1],x['matches']) for x in audit])
