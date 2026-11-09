from pathlib import Path
import json,hashlib,datetime,collections
R=Path(__file__).resolve().parent;L=R.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,o): (R/n).write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
a={}
for line in (R/'assessments.tsv').read_text().splitlines():
 n,s,loc,reason=line.split('|',3);a[int(n)]=(s,loc,reason)
selected=json.loads((R/'selected-records.json').read_text());assert len(a)==50 and set(a)=={x['record']['mathdb_id'] for x in selected}
rows=[]
for z in selected:
 x=z['record'];n=x['mathdb_id'];s,loc,reason=a[n];orig=s.replace('-converted','');meta=json.loads((R/'primary'/(orig+'.meta.json')).read_text())
 level='original_problem_body_and_internal_context'
 if n in [389108,389110,389113]:level='secondary_collection_entry_primary_access_hold'
 if n in [389212,389230]:level='primary_collection_entry_and_definition'
 if n==389291:level='related_original_context_scope_correspondence_hold'
 txt='primary/'+s+'.txt'
 rows.append({'mathdb_id':n,'url':x['canonical_url'],'title':x['title'],'literal_statement':x['statement'],'scope':x['statement'],'quantifiers':'Exactly those in literal_statement; no domain repair or parameter restriction adopted. See reason for source limitations.','statement_sha256':z['statement_sha256'],'canonical_record_sha256':z['canonical_record_sha256'],'disposition':'HOLD_primary_access' if n in [389108,389110,389113] else 'PARK_no_qualified_full_scope_mechanism','reason':reason,'evidence_level':level,'evidence':{'body':'primary/'+orig,'text':txt,'body_sha256':meta.get('sha256'),'text_sha256':sha(R/txt),'url':meta['url'],'retrieved_utc':meta['utc'],'locator':loc,'original_body_read':n not in [389108,389110,389113],'primary_statement_correspondence':'unverified' if n in [389108,389110,389113,389291] else 'bounded statement/context comparison only; not a published-version audit'},'source_version':('arXiv:2002.03233v2, 21 Dec 2020' if s=='quantum' else 'dated contributor page / workshop 9–13 Oct 2006 / downloaded body; consult metadata and body title'),'published_correspondence':'Not independently established beyond source identity/date visible in body; unversioned pages pinned by hash.','dedup_prior':{'accepted_history_id_join':'no assigned ID association located in bound r304 indexes','source_family_clearance':False,'within_assignment_related_ids':[389165,389289] if n in [389165,389289] else [],'inherited_failed_routes':'No matching assigned-ID historical route located; Cayley r363 exclusion retained as substantive adaptation policy, not retried.','registry':'HOLD; no current registry head checked; open label and empty solutions supply no novelty evidence'},'proof_section_read':False,'source_reported_resolution':'Only restricted known examples/theorems noted in reason; no asserted full resolution','successor_proof_body_review':False,'dependency_audit':'not complete','full_scope_qualified':False,'mechanism':'No qualified new mechanism; obstacles and excluded shortcuts in reason.','decisive_calculation':'None qualified; no sweep or proof attempt authorized by this screen.','certificate_size':None,'formal_dependencies':'Not audited; no Lean or manuscript produced.','novelty_gaps':['current proof registry','closest successor proof/dependency audit','published-version correspondence'],'credit':0})
put('dispositions.json',rows)
put('proposals.json',{'proposals':[],'count':0,'credit':0,'reason':'No candidate passed full-scope mechanism qualification; registry clearance remains HOLD for all.'})
put('failures.json',[
 {'stage':'metadata path lookup','detail':'Initial guessed r304 directory name did not exist; corrected using directory listing. No scientific conclusion.'},
 {'stage':'post-freeze schema inspection','detail':'A bounded corpus-head command exposed statements for unassigned IDs 1,2,3 after freeze. This was a scope-discipline error; none was investigated, copied into selected records, dispositioned or counted. No r412 statement inspected.'},
 {'stage':'primary access','url':'https://www.math.caltech.edu/SimonPapers/R27.pdf','detail':'TLS hostname mismatch; no bypass, denied-route retry or alternate-route attempt. Three assigned Simon records retain secondary-only evidence.'},
 {'stage':'source labels','detail':'Provisional filenames frey/howe/couveignes/kedlaya were not the actual authors at their respective URLs. Body titles corrected evidence mapping: frey=Desmedt, howe=Frey, couveignes=Huang–Raskind, kedlaya=Howe. Correct Couveignes/Kedlaya files fetched from explicit schedule links. No conclusion rests on provisional filenames.'},
 {'stage':'PPT extraction','detail':'Generic HTML fallback produced unusable rivest.txt/montgomery.txt from binary PPTs; preserved but never used as evidence. Guarded LibreOffice conversion generated separate *-converted.txt evidence.'}
])
put('capped-checks.json',{'guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','all_python_helpers_guarded':True,'limits':{'AS_MiB':512,'groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230},'raises':False,'runs':['freeze.py','intake.py','fetch.py (initial and three bounded followups)','extract.py','context.py','schedule.py','ppt.py','build.py','verify.py'], 'largest_observed_group_RSS_bytes':173830144,'mathematical_sweeps':0,'MathDB_requests':0,'notes':'Guard results returned in tool logs. Numerical fields are observed maxima, not an independent OS audit.'})
remote=[]
for p in sorted((R/'primary').glob('*.meta.json')):
 m=json.loads(p.read_text());remote.append({'metadata':str(p.relative_to(R)),**m})
put('provenance.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'upstream':'bindings.json frozen before scientific reading; twenty chunks verified in place','remote_sources':remote,'network_policy':'Zero MathDB/Google/GitHubAPI/raw/codeload/diff/ScienceDirect/browser/account requests. Public HTTP only; TLS failure preserved. No current registry clearance.','counts':{'additional':9,'total':39,'next':40,'new_credit':0},'root_writes':False,'history_copies':False,'exhaustive_claim':False})
(R/'SUMMARY.md').write_text('''# r414: fifty assigned statements, zero proposals

Read all fifty literal assigned statements after freezing 367 flat SHA256/size references and verifying all twenty r301 corpus chunks in place. The intake manifest and actual referenced originals were checked read-only. No upstream verifier/receipt writer ran. Exactly fifty IDs are disjoint from the 1,733 reviewed IDs, r412’s fifty reservations and 372627/372628/368940. Reservations remain unchanged.

No low-cost full-scope mechanism qualified. `dispositions.json` gives each literal scope, statement/canonical hashes, individual reason, body/text evidence, limitations and zero credit. `proposals.json` is empty. This is bounded triage, not an exhaustive corpus or literature review, a proof of hardness, or ineligibility adjudication. Source-access gaps remain HOLD; every current registry remains HOLD. No new proof, certificate, Lean or manuscript was produced; no numerical sweep ran.

Primary contributor bodies distinguish quantum versus classical models, volume-uniform interacting condensation versus the printed free-gas example, and all-copy nondistillability versus one-copy tests. The arithmetic collection defines the Mahler-measure infimum and already reports nine angular cases. Dujella’s body supplies only bounds for extremal quintuple parameters and known degree-zero/one/two polynomial bounds, not the general coefficient-independent bridge.

Workshop slides were recovered from the public schedule, including guarded PPT conversion. Their explicitness, complexity, distribution and security conditions prevent trivial substitutions: Picard-group existence is not fast composition, general LLL worst cases do not preserve ideals by isometry, hidden-order inversion is not disposed of by known-order exponentiation, and arbitrary related composites are not automatically valid RSA generator outputs. Howe’s principally-polarized threefold question is related context rather than the record’s isogeny-class question. Restricted known algorithms/examples are recorded without claiming a full published resolution. No closest-successor proof section or full dependency audit was completed; none was used to qualify a lead or infer novelty.

Three Simon entries retain secondary-only evidence after a TLS hostname mismatch on the primary PDF. No bypass/retry occurred. Other operational limitations, provisional filename corrections, the unused binary-PPT text fallback and a bounded post-freeze exposure of unassigned schema-example IDs 1–3 are preserved in `failures.json`; those IDs were not investigated or counted. No r412 statement was read.

The separate `verify.py` rechecks bound originals, the root manifest and its exact payload set, twenty chunks, literal/canonical statement identity, exact assignment/disjointness, remote body hashes and the lane’s exact manifest payload set. It exits nonzero on mismatch and prints its result only; it does not write upstream receipts. The manifest excludes only `manifest.json` and `final-receipt.json` by relative path.

Accepted counts remain **9 additional / 39 total / next 40**. No shared/index/ledger/git/public changes.
''')
print(collections.Counter(x['evidence_level'] for x in rows))
