import pathlib,json,hashlib,collections,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
def j(p):return json.loads(p.read_text())
def write(n,x):(P/n).write_text(json.dumps(x,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def h(b):return hashlib.sha256(b).hexdigest()
literal={x['record']['mathdb_id']:x for x in j(P/'literal-records.json')}
ds=[]
coverage={
399164:{'source':'ems13103.pdf','pages':[32,33],'printed_pages':[1832,1833],'passage':'Lawson cone paragraph following (3), explicit all m,n>=1 and 0<s<1 existence and uniqueness; reference [4] arXiv:1402.4173','finding':'Source explicitly says already proved; proof in cited paper not read.','proved_results_read':'Report theorem assertion only; no full proof audit.'},
399229:{'source':'ems13108.pdf','pages':[10,11],'printed_pages':[2124,2125],'passage':'Nigel Boston, GI-extension definition and final paragraph on groups without a GI-extension; references [1],[3].','finding':'Source explicitly reports two order-64 counterexamples and infinitely many 2-groups; original 1999 proof body unread.','proved_results_read':'Published report of refutation, not replay of counterexample or original body.'},
399241:{'source':'ems13108.pdf','pages':[54,55],'printed_pages':[2168,2169],'passage':'Probable Proposition 2 and following sentence identifying an elementary Smith Theory route.','finding':'Exact displayed claim present, but probable proof not supplied and scope remains questionable; unrestricted simply connected examples would yield only wording/domain correction.','proved_results_read':'Nearby probable statements and explanation, no complete proof.'},
399560:{'source':'ems13675.pdf','pages':[22,23,24],'printed_pages':[992,993,994],'passage':'Maroti, Section 1 and radical-trivial theorem at next page; bibliography.','finding':'Target log3 bound is conjectural in report; theorem proves radical-trivial case only.','proved_results_read':'Theorem statements, no proof body supplied.'},
399562:{'source':'ems13675.pdf','pages':[22,23,24],'printed_pages':[992,993,994],'passage':'Maroti, Section 1 universal-c question and polylogarithmic theorem; bibliography.','finding':'Displayed known bound has an unbounded log-log denominator; it does not imply a constant times log bound.','proved_results_read':'Theorem statements, no proof body supplied.'}}
for line in (P/'reviews.tsv').read_text().splitlines():
 id,cl,reason,disp,tech=line.split('\t');id=int(id);x=literal[id];r=x['record']
 d={k:x[k] for k in ['corpus_chunk','corpus_line','canonical_record_sha256','statement_utf8_sha256']}
 d.update({'mathdb_id':id,'statement':r['statement'],'title':r['title'],'canonical_url':r['canonical_url'],'source_url':r['source_url'],'source_reference_literal':r['references'],'independent_completeness':cl,'completeness_reason':reason,'complete_self_contained_statement':cl=='complete','disposition':disp,'technical_assessment':tech,'accepted_credit':0,'current_registry_cleared':False,'source_scope_cleared':False,'prior_cleared':False,'quantifier_scope':'Literal quantifiers retained verbatim in statement; technical assessment addresses the full stated scope.','evidence_level':{'statement':'all literal text read independently','primary':'selected passage and rendered page read' if id in coverage else 'not body-read in this lane','whole_body':'not read','successor_body':'not read','local_proof':'no new full-scope proof','full_dependency':'not audited','registry':'HOLD unavailable; no absence inference'}})
 if id in coverage:d['source_coverage']=coverage[id]
 if id==399164:d['disposition']='EXCLUDE_SOURCE_REPORTED_THEOREM';d['technical_assessment']+=' Selected primary report already asserts the exact full-scope result; no independent novelty claim.'
 if id==399229:d['disposition']='EXCLUDE_SOURCE_REPORTED_REFUTATION';d['technical_assessment']+=' Selected primary report explicitly reports known order-64 counterexamples; no new certificate developed.'
 ds.append(d)
assert len(ds)==50 and {d['mathdb_id'] for d in ds}==set(literal)
write('dispositions.json',ds);write('proposals.json',[])
counts=dict(collections.Counter(d['independent_completeness'] for d in ds))
write('coverage.json',{'literal_record_reviews':50,'baseline_literal_reviews':7483,'potential_root_reconciled_total':7533,'root_reconciliation_pending':True,'independent_completeness':counts,'complete_mathematical_statement_reviews':counts['complete'],'hypotheses':0,'credit':0,'whole_corpus_coverage':False})
write('source-coverage.json',{'selected_primary_records':coverage,'distinct_primary_reports':3,'selected_primary_records_count':5,'whole_bodies_read':0,'successor_bodies_read':0,'full_dependency_audits':0,'proof_body_clearances':0,'limit':'Known-resolution leads for other records are unverified background leads, not proof-body clearance. No significant hypothesis investment made.'})
write('bounded-checks.json',{'executed':['All 50 literal and canonical record identities checked against original chunks.','Selected report theorem/refutation and quantifier comparisons.','Known polylogarithmic bound does not supply a uniform positive linear-log coefficient because its denominator is unbounded.'],'numerical_sweeps':0,'new_full_scope_certificates':0,'planned':[]})
write('failures.json',{'failed_checks':[{'operation':'first PDF render helper','error':'TypeError: scale-to argument supplied as int instead of string','guard_exit':1,'resolution':'Corrected argument type under unchanged guard; four images generated, bound then inspected.'}],'deviations':['Initial intake listing used recursive file enumeration for exact-payload hashing only; no historical tree copied or expanded into lane.','AGENTS-required source catalogue opening displayed an unrelated initial catalogue excerpt; no scientific use or extra coverage claimed.','PDF selections exposed adjacent contributions on report pages 33 (13103), 11-12 and 55 (13108), 22 and 24-25 (13675). Page 11 was initially selected instead of page 10 for GI text. Subsequent correct page 10 read. Adjacent contributions excluded from findings and coverage.'],'finalizer_bootstrap_failure':{'error':'Verifier originally required excluded final receipt to exist before generating it','guard_exit':1,'resolution':'Exact payload check now subtracts the two allowed exclusions; no listed payload omitted; negative tests rerun'},'new_http_failures':[],'stopped_routes_preserved':['MathDB all requests (429 HOLD)','Google/GitHub API/raw/codeload/diff','ScienceDirect/browser/preview/TLS bypass','Author Gorenstein PDF TLS r642','AIM/Kourovka/EGRES/AIProofWatch','DMGT TLS','ProjectEuclid challenge','ResearchGate 403','OEIS A274199/internal HTTP403 r542','DOI10.1093/imrn/rnz305 academic.oup.com HTTP403 r618'],'registry':'Unavailable HOLD; zero requests and no absence-of-hits inference.'})
write('administrative-gates.json',{'assignment':'root-mathdb-breadth-intake-r663/queue-r664.json and reserved-ids-r664.json','baseline':7483,'counts':{'additional':9,'total':39,'next':40},'r304_exclusions_and_history':'bound and consulted; no assigned ID overlap in accepted lookup; family scope and exclusion rules retained','r363':'Cayley 364119 excluded as source-adaptation; no variant credit','current_adjudications':'r663 bound and read; 338290/339564/372627 retired;337963 parked;338408 parked;338366 excluded with text/figure reconstruction and unread-journal caveats','other_reservations':'r662 continues; r628 rate-limit held untouched and uncounted','no_shared_edits':True,'integrity_is_not_scientific_acceptance':True})
summary=f'''# Sol breadth r664

Reviewed all 50 assigned literal records independently; zero substitutions, zero proposals and zero credit. Baseline 7,483 literal reviews; these 50 await root reconciliation (potential total 7,533). Counts remain 9 additional / 39 total / next 40. This is not full technical corpus coverage.

Independent classifications: {counts}. Each row retains its reason, full exact statement, quantifier-sensitive technical assessment, original corpus chunk/line, UTF-8 statement hash and canonical record hash.

Five selected primary record passages across three reports were read; four bound renderings inspected. 399164 is explicitly reported already proved; 399229 is explicitly reported refuted by known order-64 examples. These are report-body findings, not original-proof replays. 399241 remains scope/domain HOLD, with a source-mentioned Smith-theory route and no full proof. 399560/399562 retain an arbitrary-group obstruction; the source's radical-trivial theorem and weaker general bound do not settle them. Other public-resolution recollections are leads only. No whole-body, successor-body, full dependency or registry clearance is claimed.

All 20 original r301 chunks and eight frozen inputs were verified in place, including inventory-manifest binding. Intake exact payload and 44 direct original/copy pairs checked independently without executing upstream verify.py. All three reserved sets are disjoint from one another, protected IDs and 7,483 coverage. Only assigned-lane artifacts written; no corpus copied, no git or shared changes.

Zero MathDB requests. All stopped routes and privacy restrictions retained. Registry unavailable => HOLD. 338366 remains excluded with text/figure reconstruction and unread-journal limitations; 338408 parked. r628 untouched and uncounted; r662 unaffected. Source/prior/substantive and scientific-acceptance gates remain HOLD; integrity PASS is not mathematical PASS.

Failures/deviations: corrected one render-helper type error under the unchanged guard; incidental adjacent-report and catalogue content exposure disclosed in failures.json without extra scientific coverage. No HTTP failures or route retries. No heavy computation or new formal certificate.

Run `sh verify.sh` for the independent read-only verifier under the fixed guard. Manifest excludes only itself and final-verification-receipt.json. Final receipt binds exact manifest hash/size; bounded hash, size and extra-file rejection tests are recorded separately.
'''
(P/'SUMMARY.md').write_text(summary)
def manifest():
 files=[]
 for f in sorted(P.rglob('*')):
  if f.is_file() and f.name not in ['manifest.json','final-verification-receipt.json']:
   raw=f.read_bytes();files.append({'path':str(f.relative_to(P)),'size':len(raw),'sha256':h(raw)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files})
manifest()
neg=[]
for mode in ['hash','size','extra']:
 r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--negative-'+mode],capture_output=True,text=True)
 assert r.returncode!=0 and ('mismatch' in r.stderr),r.stderr
 neg.append({'mutation':mode,'returncode':r.returncode,'rejected':True,'method':'in-memory expected hash/size or observed payload-name perturbation; no original file changed'})
write('negative-tests.json',neg);manifest()
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True)
assert r.returncode==0,r.stderr
raw=(P/'manifest.json').read_bytes()
write('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(raw),'manifest_size':len(raw),'verification':json.loads(r.stdout),'negative_tests':neg,'mathematics_and_novelty':'HOLD, not certified','guard':'fixed 512MiB AS/groupRSS; CPU210s; wall230s; python3 -B; BLAS/OMP=1'})
print(r.stdout);print(json.dumps({'manifest_sha256':h(raw),'manifest_size':len(raw),'classifications':counts}))
