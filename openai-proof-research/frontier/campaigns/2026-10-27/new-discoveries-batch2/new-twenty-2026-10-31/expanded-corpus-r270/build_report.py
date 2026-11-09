import pathlib,json,hashlib,datetime,resource,os,re
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def dump(n,o): (p/n).write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
reservation=json.loads((p/'reservation.json').read_text()); fixed=list(map(str,reservation['ids'])); expect=(p/'reservation.sha256').read_text().split()[0];assert H((p/'reservation.json').read_bytes())==expect
r=json.loads((p/'literal-records.json').read_text()); assert set(r)==set(fixed)
# Verify literal bytes in immutable corpus. This is extraction/audit only, no search over mathematical instances.
for k,v in r.items():
 b=(p/'raw'/f'{k}.jsonl').read_bytes();assert H(b)==v['raw_sha256'];f=pathlib.Path(v['chunk']);assert H(f.read_bytes())==v['chunk_sha256'];
 with f.open('rb') as a:
  for i,l in enumerate(a,1):
   if i==v['line_1based']:assert l==b;break
 assert json.loads(b)==v['record'];v['statement_sha256_utf8']=H(v['record']['statement'].encode())
dump('literal-records.json',r)
# Status is a research disposition, never an acceptance award.
D={
'371975':('PARK_UNIFORM_LOWER_BOUND','2512.09674 Conjecture 1.2, definitions of stable vertices; companion 0912.4748 Conjecture 1 and 1712.03456 Theorem 1.1 read selectively.','Need all-r stable-hypergraph chromatic lower bound. r=2, selected primes or powers do not settle it.'),
'317154':('EXCLUDE_PUBLISHED_RESOLUTION','0803.0855 pm-graph and phi definitions selectively; 0901.3945 Theorem 2.9, proof dependencies 5.21/7.8 and local proof passages.','Cinkir supplies positive t(g) and exactly the separating-edge coefficients. No new discovery.'),
'317335':('EXCLUDE_PUBLISHED_RESOLUTION','0805.0082 Conjecture 5.4 across v1/v2/v3; 1101.2648 Theorem 3.5 boundary-matrix statement and Corollary 3.6.','Later planar torsion-free result plus original nonplanar 2-torsion settles the intended graph class. No disconnected-graph wording correction claimed.'),
'317369':('EXCLUDE_PUBLISHED_RESOLUTION','0805.2416 Conjecture 1.4.9 and preceding symmetry; 1101.4441 Theorems 1.1/1.2, Section 3 beginning and final proof (3.3)-(3.4).','Henderson-Wachs proves exact all-cycle-type t-unimodality.'),
'317465':('PARK_HILBERT_SERIES_BRIDGE','0806.2936 Conjectures 4.6/4.17 and nearby coheight passages; 0901.1574 selective statements only.','No algebraic-Hilbert-series/coheight bridge. Source calls type-B m=1 conjectural, unlike record prose.'),
'317500':('EXCLUDE_KNOWN_CONSTRUCTION_BODY_LIMIT','0806.4135 Section 2.2 definitions and Conjecture 2.3; later primary-search excerpts only, full IACR body 403.','Six-bit Dillon APN permutation is already published; known-example formalization excluded. Construction/proof-body reading incomplete.'),
'317546':('PARK_EXACT_THRESHOLD','0807.1827 Conjecture 3 in v1/v2 and approximate Corollary 4; source sharpness context.','Approximate/sufficiently-large result is not the exact all-n degree sequence conjecture.'),
'317765':('PARK_TOPOLOGICAL_COMPATIBILITY','0809.4364 ending of scanning homotopy, Conjectures 3.3/3.4 and proposed contraction map.','No quotient-continuous arbitrary-genus homotopy fixing the tropical subspace pointwise.'),
'317808':('HOLD_LATER_SUBSUMPTION_AND_LITERAL_NORMALIZATION','0809.4983 Conjecture 30, equation/graph context and Proposition 28 statement; 0907.1715 abstract and selected main-result passages.','Need actual printed basis independence and later Poisson-homology identification. Scalar multiples are an excluded normalization correction.'),
'317909':('PARK_BOUNDED_MULTIPLICITY_GAP','0811.0290 latest Section 1 through Conjecture 2, preceding unique-representation proof; v3-v5 target and v1-v2 differing Conjecture 2 compared.','No extension from unique coefficients to bounded positive coefficients. Residue/counting routes fail; see sustained attempt.'),
'317997':('EXCLUDE_PUBLISHED_RESOLUTION','0812.1165 Conjecture 2.1, torus/cylinder distinction and Proposition 4.9 context; Jonsson 2009 Introduction and final proof passages.','Jonsson EJC 16(2) R5 proves the identical odd-cylinder formula. The record incorrectly routes status to the earlier 2006 torus work.'),
'316253':('PARK_FACET_CLASSIFICATION_GAP','0704.0918 Section 5 conventions, Theorem 5.1 and proof, Corollaries 5.2/5.3 and proofs, Conjecture 5.4 in v1/v2.','Facet-distance point has branching slack 4-deg(v); irredundancy, lattice primitivity, uniqueness, and actual-ring Gorenstein bridge remain unproved.'),
'316290':('PARK_GENERAL_TWISTED_GRAPH_EXISTENCE','0704.3424 Section 3.4 Ringel refutation; Definitions 13.12, Conjectures 13.15/13.16 in both versions, neighboring representation setup.','Reference refutation is about Ringel, not assigned Conjecture 13.16. Cubic construction is already printed; general orientation/order certificate absent.'),
'316540':('PARK_INTENDED_ODD_WALK_POWER','0708.0704 exact-walk power definition, latest Conjecture 3 and Tardif paragraph; earlier-version target locators incomplete.','Distance-power star example changes the definition. Tardif bounded-class theorem does not supply the claimed explicit planar bound.'),
'316812':('PARK_TWIN_PRIME_STRENGTH','0711.0865 weight/level/gap definitions and Conjecture 2 in v1-v4; historical r82 record reviewed.','Weight 3 requires gap 2; a finite sample or bounded-gap theorem cannot prove infinitude.'),
'316821':('EXCLUDE_MISSING_HYPOTHESIS_PARK_INTENDED','0711.1262 all-sets-are-multisets convention, maximal sequence motivation, Property B definition and multiplicativity/small-prime Proposition 4.','Literal singleton counterexample is only a missing maximal-length/domain correction. Intended maximal zero-sum-free claim has no all-primes proof.'),
'316833':('EXCLUDE_SOURCE_PRINTED_REFUTATION','0711.1738 latest Appendix B.1 surrounding argument, references to Tables 15/16 and stated strip families. Earlier v1 exact locator failed.','Source explicitly reports B5 positivity false via printed strips. No exact numerical certificate checked here; no printed-object formalization for credit.'),
'316835':('PARK_EXACT_QUADRANGULATION_WITNESS','0711.1738 latest Appendix B.2/B.3 and diced-lattice caveat.','A thermodynamic critical point or complex zeros do not establish a finite real chromatic root >=3. No eligible exact graph/witness.'),
'316883':('PARK_EXACT_CYCLE_LENGTH','0711.4394 v1/v2 Introduction, printed examples, Theorem 1.4, Proposition 2.1 and proof.','Separator-clique, parity-breaking bipartite and regular high-girth routes do not supply a witness; uniform exact-length shortening lemma absent.'),
'316930':('PARK_REGULARITY_PARTITION_BRIDGE','0712.2308 Conjecture 3.9 and preceding relation to Soleyman Jahan; historical poset source-family notes routed.','Bottom-degree regularity bound is not Stanley-depth top rank; no exact duality bridge or new nonpartitionable obstruction certified.')}
receipts=[json.loads(x) for x in (p/'fetch-receipts.jsonl').read_text().splitlines()]
limits=['Latest journal/correction bodies not systematically obtained or read; no current-open certification.', 'Not all citing primary bodies or printed objects/figures were read. No witness proposed as source-eligible.', 'No complete current registry commit/tree or worldwide priority clearance.', 'No Lean, independent acceptance review, manuscript or extracted replay. Pi must await root qualification.']
results={}
for k in fixed:
 v=r[k];o=v['record']; a=o['source_url'].split('/')[-1];disp,depth,gap=D[k]
 versions=sorted(set(re.findall(r'\[v(\d+)\]',(p/'sources'/f'{a}.abs.html').read_text())),key=int)
 results[k]={'mathdb_id':int(k),'title':o['title'],'canonical_url':o['canonical_url'],'literal_statement':o['statement'],'statement_sha256_utf8':v['statement_sha256_utf8'],'raw_provenance':{j:v[j] for j in ['chunk','chunk_sha256','line_1based','raw_sha256','raw_newline_preserved']},'raw_artifact':f'raw/{k}.jsonl','full_parsed_record':o,'disposition':disp,'review_depth':{'literal_record':'Entire statement and parsed record read.','primary_passages_actually_read':depth,'listed_arxiv_versions':versions,'version_passage_inventory':'version-target-passages.json; some literal locators failed or selected a wrong nearby passage, explicitly not counted as full target review. All 40 original-source version PDFs fetched.','full_every_version_proof_audit':False,'all_figures_visually_read':False,'latest_journal_all_citing_bodies_cleared':False},'ordinary_attempts':'ATTEMPTS.md','precise_remaining_gap_or_exclusion':gap,'history_evidence':['history-paths.txt','history-hits.txt','history-search-log.json','HISTORY.md'],'source_inventory':'source-inventory.json','source_receipts':[x for x in receipts if a in x['url']],'current_registry':'registry-screen.json','qualification_limits':limits,'candidate_qualified':False,'pi_execution_requested':False,'lean_endpoint':None,'root_acceptance':False,'credit_claimed':False}
dump('results.json',results)
inventory=[]
for f in sorted((p/'sources').iterdir()):
 if f.is_file():inventory.append({'path':str(f.relative_to(p)),'sha256':H(f.read_bytes()),'bytes':f.stat().st_size,'read_depth':'Downloaded/extracted only unless expressly named in results.json, ATTEMPTS.md or version-target-passages.json. Presence is not reading.'})
dump('source-inventory.json',inventory)
terms=['Kneser','Gorenstein','Poisson homology','Adamus','Dobbertin','APN','Stanley depth','Zhang','Nash-Williams','Eulerian','quadrangulation']
registry=[]
for f in sorted((p/'sources').glob('registry-*')):
 s=f.read_text();registry.append({'path':str(f.relative_to(p)),'sha256':H(f.read_bytes()),'matches':[l for l in s.splitlines() if any(re.search(r'\b'+re.escape(t)+r'\b',l,re.I) for t in terms)],'role':'Current lawful public raw routing evidence only. Not all code, theorem bodies or a complete current tree.'})
dump('registry-screen.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'github_api':'Not called: inherited 403 respected.','current_head_sha':'NOT ESTABLISHED','receipts':'fetch-receipts.jsonl','sources':registry,'body_reading':'APN Kasami catalogue entry read; it concerns a Kasami derivative-image result, not an even-dimensional APN permutation construction. Other generic Gorenstein-projective and Poisson-integral hits are different statements. No live complete clearance.','cached_catalogue':'Project sources/CONTENTS.md and pinned sources/upstream.json read as routing evidence; campaign historical receipts retained by reference.'})
assert list(results)==fixed and len(results)==20
actual=H((p/'reservation.json').read_bytes());assert actual==expect
dump('reservation-check-after.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'expected_sha256':expect,'actual_sha256':actual,'matches':True,'same_ordered_20_ids':True,'raw_chunk_and_statement_audit':True})
dump('execution-audit.json',{'scripts':['fetch.py','build_report.py'],'python_invocation':'python -I -B with actual lane-local script paths','limits':{'cpu_affinity_max_cpus':2,'RLIMIT_CPU_seconds':120,'wall_wrapper_seconds':140,'RLIMIT_AS_bytes':6*1024**3},'jobs':'HTTP retrieval, pdftotext and exact byte/hash checks only; no Lean, numerical solver or graph enumeration.','fetch_logs':['fetch-base.log','fetch-versions.log','fetch-extra.log','fetch-more.log','fetch-final.log'],'usage':str(resource.getrusage(resource.RUSAGE_SELF)),'limitations':'Some initial short read-only extraction commands were inline Python, before durable scripts were written. No external cache configured by these scripts.'})
manifest={str(f.relative_to(p)):H(f.read_bytes()) for f in sorted(p.rglob('*')) if f.is_file() and f.name!='manifest.json'}
dump('manifest.json',{'sha256':manifest,'self_excluded':True,'reservation_sha256':expect})
print('PASS: exact 20 keys; all raw lines/chunks/statements audited; reservation unchanged',actual)
print('source files',len(inventory),'receipts',len(receipts),'original listed versions',sum(len(x['review_depth']['listed_arxiv_versions']) for x in results.values())-len(results['316833']['review_depth']['listed_arxiv_versions']))
