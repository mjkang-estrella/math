from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).parent;L=R.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(n,o):(R/n).write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
rows=json.loads((R/'records.json').read_text());assess={}
for line in (R/'assessment.tsv').read_text().splitlines():
 n,scope,reason=line.split('\t');assess[int(n)]=(scope,reason)
assert len(assess)==50 and set(assess)=={x['mathdb_id'] for x in rows}
# These are bounded historical identity checks, not live or family-level clearance.
historical={}
D=L/'root-mathdb-accepted-exclusions-r304'
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 text=(D/name).read_text()
 for x in rows:
  if str(x['mathdb_id']) in text:historical.setdefault(x['mathdb_id'],[]).append(name)
assert not historical
out=[]
for x in rows:
 scope,reason=assess[x['mathdb_id']]
 out.append({'mathdb_id':x['mathdb_id'],'url':x['canonical_url'],'source_url':x['source_url'],'source_name':x['source_name'],'literal_statement':x['statement'],'literal_sha256':sha(x['statement'].encode()),'canonical_record_sha256':sha(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'literal_review':True,'quantifiers_and_scope':scope,'scope_status':'literal reading; primary-source hypotheses unverified','disposition':'PARK_NO_SOURCE_QUALIFIED_LOW_COST_FULL_SCOPE_MECHANISM','evidence_level':'literal_full_statement_review_only','reason':reason,'selected_primary_body_read':False,'proof_section_read':False,'dependency_audit':False,'primary_source_version':None,'published_correspondence_verified':False,'successor_proof_bodies_read':False,'dedup_prior_status':{'reserved_id_disjoint_from_reviewed_1283':True,'reserved_id_disjoint_from_other_active_50':True,'focused_ids_disjoint':True,'r304_exact_id_hit':False,'family_level_prior_clearance':False,'r363_rule_applied':'Do not count source-internal refutations, smaller witnesses, or source-demonstrated adaptations.'},'current_registry_clearance':'HOLD: current registry unavailable under request restrictions; no old-cache clearance','source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0,'proposal':False})
put('dispositions.json',out);put('proposals.json',[])
fail=json.loads((R/'failures.json').read_text())
for e in json.loads((R/'source-provenance.json').read_text()):
 if 'error' in e:fail.append({'phase':'selected_primary_fetch',**e,'action':'No extraction/read, TLS bypass, alternate host, browser, denied-route retry or source qualification'})
mismatch=[]
for e in json.loads((D/'bindings.json').read_text()):
 p=Path(e['original']);actual={'size':p.stat().st_size,'sha256':sha(p.read_bytes())}
 if actual['sha256']!=e['sha256'] or (e.get('size',e.get('bytes')) is not None and actual['size']!=e.get('size',e.get('bytes'))):mismatch.append({'path':str(p),'historical_expected':{'size':e.get('size',e.get('bytes')),'sha256':e['sha256']},'actual_at_freeze':actual})
put('historical-binding-mismatches.json',mismatch);put('failures.json',fail)
put('coverage.json',{'literal_full_statement_reviews':50,'selected_primary_source_requests':3,'successful_primary_bodies_read':0,'successor_proof_sections_read':0,'complete_dependency_audits':0,'current_registry_clearances':0,'qualified_briefs':0,'accepted_credit':0,'scope':'Only the exact fifty reserved IDs. Corpus hash verification is not scientific review of the corpus. No exhaustive coverage claim.','other_active_ids_investigated':0,'mathdb_requests':0,'historical_exact_id_scan':'No assigned-ID string hits in the two r304 summaries; does not clear families or current public literature.'})
put('registry-status.json',{'status':'HOLD','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'current_heads':None,'reason':'Current public registry not established: GitHub API/raw/codeload/diff and MathDB requests prohibited; no browser/accounts. No current clearance inferred from pinned records.','requests':0,'significant_new_discovery_investment':False})
(R/'source-reading.md').write_text('''# Source qualification record

All fifty literal statements were read in full from verified in-place corpus records, retained in records.json and individually in dispositions.json. The immutable r301 manifest was checked against all twenty original corpus chunks before reading them. Tags played no scientific role.

Selected source routes: graphstructureapp sections 2 and 3 for the potentially short graph questions, and freebycyclic section 1 for effective coherence (385263). All three HTTPS requests failed certificate hostname verification for aimpl.org. Exact URL, UTC, exception and access method are retained in source-provenance.json and failures.json. No response body was obtained: there is no body hash to report and no extraction. The HTTPS form of the source URL was attempted once per selected page. No HTTP fallback, host substitution, TLS bypass or retries followed. Subsequent distinct pages encountered the same certificate failure; the domain is now stopped.

Thus primary definitions, source-internal examples/theorems and successor proof sections were NOT read. No public resolution, novelty, source-version equivalence, theorem applicability or family-level absence is claimed. In particular, the effective-coherence question was parked without asserting that a known existential coherence result automatically supplies an algorithm. Quantum enumeration likewise was not promoted from an amplitude-amplification slogan. No large search or finite graph sweep was run.

The bound r304 accepted-exclusions and historical-dispositions files supplied administrative no-recount context. A bounded exact-ID scan found no assigned IDs; this is not literature clearance. The bound r363 disposition excludes source-already-demonstrated refutations/adaptations and overrides its older favorable assessment. No smaller witness was sought. Ledger baseline is 9 additional / 39 total / next 40, unchanged by this lane.

The initial r304 checker incorrectly required a size field absent from its SHA-only bindings. Both actual original hashes match the historical bindings. The initial assertion and subsequent metadata-reader KeyError are retained in helper-failures.txt. Flat references additionally record actual sizes. historical-binding-mismatches.json is empty after the corrected comparison. Root r395 bindings and its manifest matched, and its receipt-writing verifier was never executed. No historical trees or corpus chunks were copied.
''')
(R/'SUMMARY.md').write_text('''# r396: fifty literal reviews, zero qualified briefs

All **50 assigned IDs** received individual full-statement reviews. **Zero proposals and zero credit**. See dispositions.json for exact statements, hashes, quantifiers, objections and evidence levels. proposals.json is an empty array.

The root r395 intake was checked read-only. Its reservation is exactly this lane's fifty and disjoint from 1,283 reviewed IDs, Sol r394's active fifty and focused IDs 372627/372628/368940. All twenty r301 corpus chunks were verified in place before content inspection. Flat SHA256/size references to intake, actual originals, historical exclusions and r363 disposition were frozen first in read-only input-bindings.json. No upstream verifier or receipt was run or changed.

**Evidence limits:** 50 literal reviews; 3 selected source requests; 0 successful primary-body readings; 0 successor proof-section readings; 0 complete dependency audits; 0 current registry clearances. The selected AIM requests failed certificate hostname verification, retained in source-provenance.json and failures.json. Registry status is **HOLD**. The old open labels and empty solutions were not used as novelty evidence. Source version/published correspondence remains unverified. No briefs, numerical sweeps, Lean or manuscript were produced.

The apparent easy routes generally require omitted definitions, solve only instances/subparts, or offer tautological endpoints. The record-specific reasons distinguish these from hard full classifications and algorithms; none is asserted to be publicly resolved without a primary proof. No scientific conclusion is inferred about unassigned records. Other active reservations were not investigated.

The initial freeze and first reporting helper failed on assumptions about absent size fields in r304 SHA-only bindings. Both failures are retained in helper-failures.txt. Corrected checks show both historical original hashes match; historical-binding-mismatches.json is empty. Root intake hashes passed; no upstream bytes were repaired or altered. Final verification independently rehashes actual frozen originals, root payload/bindings, all twenty chunks, canonical records/statements, assignment/disjointness and the exact lane payload set, failing nonzero on any mismatch. See final-receipt.json for the result.

No shared/index/reservation/count/git/public changes. Baseline remains **9 additional / 39 total / next 40**.
''')
print('WROTE',len(out),'dispositions; zero proposals; historical mismatches',len(mismatch))
