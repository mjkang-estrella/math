import pathlib,json,hashlib,subprocess,datetime,re
D=pathlib.Path(__file__).resolve().parent;P=D.parent;B=P.parent;h=lambda b:hashlib.sha256(b).hexdigest();r=json.load(open(D/'reservation.json'));rec=json.load(open(D/'exact-records.json'));C=B/'lanes/pi-mathdb-full-corpus-inventory-r301';m=json.load(open(C/'manifest.json'))
checks=[]
for x in m['files']:
 if re.fullmatch(r'corpus/mathdb-normalized-chunk-\d+\.jsonl',x['path']):
  a=h((C/x['path']).read_bytes());checks.append({'path':x['path'],'expected':x['sha256'],'actual':a,'ok':a==x['sha256']})
for f,v in r['input_hashes'].items():
 a=h(pathlib.Path(f).read_bytes());checks.append({'path':f,'expected':v,'actual':a,'ok':a==v,'context':'mutable administrative ledger if ledger.json; otherwise reservation input'})
(D/'input-verification.json').write_text(json.dumps(checks,indent=2));print('input checks',len(checks),'mismatches',[x['path'] for x in checks if not x['ok']])
# Read inherited accepted/excluded families without copying historical trees.
fam=[]
for f in [C/'frozen/accepted-exclusions.json',C/'frozen/historical-dispositions.json']:
 o=json.loads(f.read_text());fam.append({'path':str(f),'sha256':h(f.read_bytes()),'parsed_type':type(o).__name__,'exact_id_mentions':[i for i in r['ids'] if re.search(r'\b'+str(i)+r'\b',json.dumps(o))]})
(D/'inherited-family-check.json').write_text(json.dumps(fam,indent=2))
notes={
359822:'HOLD: measure-support statement needs the actual topological surface-counting measure definition and a genus-selective asymptotic estimate. No primary body read.',
359838:'HOLD: source Conjecture 1.2 read; shared r-partition and uniformity conventions matter. r=1 endpoint is not an eligible route. No full combinatorial covering mechanism for r>=4.',
359840:'HOLD: source Definition 1.5 and Conjecture 4.1 recovered. Loom requires orthogonality, minimum covers and mutual minimum-cover closure. A random cross-intersecting pair is not a loom. Perfect fractional matching obstruction remains.',
359956:'HOLD: must recover weighted OSASM statistics and the range n before coefficient testing. The generic ASM resolution quotation in metadata cannot clear this refined claim.',
359993:'HOLD: general triangle-free coloring at degree 5 needs a full structural coloring argument or a genuine 5-chromatic regular triangle-free witness; no such construction obtained.',
360014:'HOLD: small directed path-cover certificate could refute, but no graph witness and no complete directed definitions recovered from primary body.',
360015:'HOLD: full mixed-degree path-cover bound; endpoint delta=Delta=0 is ineligible wording route. No nontrivial path-cover obstruction obtained.',
360045:'HOLD: universal O(sqrt(d)) claim requires an unbounded family, not a fixed finite weak-degeneracy computation. Delete/save semantics not recovered from primary body.',
360062:'EXCLUDE_ROUTINE_SOURCE_BRIDGE: source Theorem 2.4 and its complete two-case proof read. Perfect graphs have no induced C5 (chi(C5)=3, clique number=2); hence diameter 2 case follows directly. Diameter 1 is complete and any pair percolates. MathDB also confuses perfect with chordal; neither gives novelty.',
360088:'HOLD: genericity, PDE solution class and extension regularity are not reconstructed. No feasible literal Lean route identified.',
360094:'HOLD: matching is a basis-wise multiplicative avoidance condition requiring a source definition; degree condition alone does not supply a proof. No primary body read.',
360181:'HOLD_PRIOR_RESOLUTION_LEAD: primary introduction explicitly attributes a refutation for n>=3,m>=2 to Hadwin-Larson [18]. That original counterexample proof body was not retrieved/read; do not rediscover or treat as novelty-cleared.',
360219:'HOLD: source Conjecture 5.6 read with parity-code lower-bound discussion. Known two-point and even-parity-code constructions only reproduce asserted lower bounds; no upper bound for arbitrary finite point sets. No proof-body clearance for new mechanism.',
360241:'HOLD: finite graph quantifiers require nonvacuous k-connectivity and longest-path semantics; k exceeding order is not an eligible endpoint route. No substantive intersection proof.',
360249:'HOLD: chi-boundedness quantifies over all induced-pattern-free ordered graphs; finitely many matching pattern tests cannot resolve it.',
360262:'HOLD: needs a properly colored cycle of every admissible even length through each vertex. A Hamiltonian cycle alone would not match endpoint; no source definitions or counterexample.',
360272:'HOLD: Davenport constant and exact-length zero-sum invariant require source semantics. No group-wide proof; parameter cases alone excluded.',
360353:'EXCLUDE_SOURCE_THEOREM: primary Theorem 1.1 exactly states the extremal inequality and uniqueness; proof closing paragraph invokes Corollary 2.3 and Lemmas 3.1-3.4. Statement and proof closure read, not an independent audit of all preceding case lemmas.',
360354:'HOLD: source Conjecture 2 is all k; its k=2 consequence of Theorem 1.1 is known and cannot settle the full reserved statement. No general all-k eigenvalue proof.',
360371:'HOLD_SUSTAINED: exact source Conjecture 6 and published Conjecture 6.1 recovered; affine rank and XOR quad semantics investigated. Exhaustive 16-card and larger constrained searches yield no witness. Rank-sensitive energy lemma remains unproved. See mathematical-attempts.md.',
360391:'HOLD: constant must be universal over infinite transitive graphs; finite-degree examples or small graph simulations do not decide it.',
360455:'HOLD_SOURCE_GAP: admissible network vectors and deviation-angle definition absent in literal record; no qualified endpoint without actual source definition.',
360474:'HOLD: asymptotic n0,C threshold needs a resolvable design embedding argument. Finite counterexamples cannot refute arbitrary constants.',
360482:'HOLD: c independent of uniformity and ground set requires asymptotic odd-sunflower bound, not a finite family count.',
360483:'HOLD: base-union bound needs exact sunflower convention and unbounded-k mechanism; fixed uniformity examples do not establish failure of all exponential constants.',
360519:'HOLD: genericity and level-k hypertriangulation refinement semantics needed before testing maximal versus maximum. No primary definitions read.',
360525:'HOLD: o(n) maximum-degree condition requires asymptotic quantified source formulation. Literal finite bound not yet recovered.',
360540:'HOLD: actual Bessel kernels, branch choices and integration meaning not recovered. Divergence outside source convergence hypotheses is an ineligible paraphrase correction.',
360543:'HOLD_SOURCE_GAP: square/non-square has specialized source meaning; no interpretation inferred from ordinary congruence-group terminology.',
360639:'HOLD: expected height over linear extensions and constant infinite product require primary semantics; no exact extremal family beating the constant.',
360651:'HOLD: multipartite hypergraph list coloring bound universal in large Delta; no full extension beyond bipartite conjecture.',
360672:'HOLD_PRIOR_RESOLUTION_LEAD: primary source Conjecture 1 and preceding definitions explicitly report Schrijver refutation. Original Schrijver proof body not read, so this is a documented old-result lead rather than a newly audited proof.',
360673:'HOLD: source mixed orientation claim is not implied by unweighted dijoin approximate packing without a new bridge. No such bridge proved.',
360677:'HOLD_SCOPE: source proves admissible case via Theorems 1.3 and 1.12, but Remark 1.8 explicitly notes Schleimer does not assume natural PMod action. Cannot silently identify full literal scope with admissible theorem. Proof transfer excerpts read; unrestricted case unresolved here.',
360705:'HOLD_SUSTAINED: source Definition 2 and Conjecture 1 recovered. Every rainbow committee must be irredundant. Exhaustive labeled graphs <=6, seeded random and planted tripartite families found no witness; recoloring lemma unresolved. Publisher body 403 and unread.',
360728:'HOLD: monotone symmetric exchange sequence of length rank is required; generic basis exchange alone does not give it. No full matroid mechanism.',
360754:'HOLD: distinguish ordinary U(g) from restricted enveloping algebra and recover field hypotheses. Source-only special classes cannot resolve full KW1.',
360758:'HOLD: dimension-index convention requires primary reading before cross-polytope tests; d=0 or dimension-shift corrections are not eligible discoveries.',
360770:'HOLD: interval labeling convention and exact QSym involution/statistics needed. Testing arbitrary relabelings risks paraphrase-only counterexample; no primary definitions read.',
360836:'HOLD: b-coloring finite graph search possible but no new graph obstruction found or attempted; degree-zero and disconnected Petersen variants require original source scope, not loophole investment.'}
primary={359838:('2309.03735','Conjecture 1.2 and conventions; selected introduction only'),359840:('2309.03735','Definition 1.5, Lemmas 1.7-1.12 proofs, Conjecture 4.1; selected body'),360062:('2309.13138','Section 2 definitions, Lemmas 2.1-2.2 and full Theorem 2.4 proof'),360181:('2310.00476','Section 1.1 conjecture and prior-result attribution; original refutation body unread'),360219:('2310.02839','Section 5 Conjecture 5.6 and lower-bound discussion; general upper-bound proofs unread'),360353:('2310.08880','Conjecture 3, Theorem 1.1, final proof closure only; case lemmas not audited'),360354:('2310.08880','Conjecture 2 and k=2 bridge statement only'),360371:('2310.09695','Sections 2-5 definitions, Theorem 2 proof, complement/conditional extremizer excerpts; published counterpart Conjecture 6.1 read'),360672:('2311.04337','Section 1 dicut/dijoin definitions, Conjecture 1 and attribution; Schrijver body unread'),360673:('2311.04337','Introduction only; exact mixed-graph conjecture body not read'),360677:('2311.04356','Definitions 1.2/1.5, Conjecture 1.7, Remark 1.8, Theorem 1.12 and proof-transfer excerpts; not full HHS proof'),360705:('2311.06161','Section 1 private-neighbor definitions, Definition 2, Proposition 3 proof, Conjecture 1; publisher body unread')}
results={}
for i in r['ids']:
 x=rec[str(i)];o=x['record'];entry={'mathdb_id':i,'title':o['title'],'canonical_url':o['canonical_url'],'literal_statement':o['statement'],'statement_sha256_utf8':h(o['statement'].encode()),'raw_provenance':{k:v for k,v in x.items() if k!='record'},'raw_file':f'raw/{i}.jsonl','source_url':o['source_url'],'inherited_matches':{'review_note_matches':[],'administrative_reservation_match':True,'substantive_old_exclusion_found':False,'search_receipts':['history-review-matches.txt','history-search.txt'],'limits':'bounded batch review-file search; broader first search had per-file cap and hash/number false positives; no global nonreview assertion'},'new_review_depth':{'literal_statement_read':True,'primary_body':primary[i][1] if i in primary else 'unread','mathematical_attempt':'sustained' if i in [360371,360705] else 'source bridge' if i==360062 else 'scope/tractability assessment only'},'outcome':notes[i].split(':')[0],'assessment':notes[i],'accepted_credit':0,'lean_endpoint':None,'remaining_lemma':notes[i].split(': ',1)[1]}
 if i in primary:
  f=D/'sources'/(primary[i][0]+'.pdf');entry['source_pdf_sha256']=h(f.read_bytes());entry['source_text_sha256']=h(f.with_suffix('.txt').read_bytes());entry['source_receipt']='receipts.jsonl'
 results[str(i)]=entry
assert len(results)==40 and set(map(int,results))==set(r['ids'])
(D/'results.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
lean=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean');lf=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json')
env={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean_binary':str(lean),'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'lean_binary_sha256':h(lean.read_bytes()),'mathlib_requested_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','lake_manifest_path':str(lf),'lake_manifest_sha256':h(lf.read_bytes()) if lf.exists() else None,'mathlib_manifest_entries':[x for x in json.load(open(lf)).get('packages',[]) if x.get('name')=='mathlib'] if lf.exists() else [],'formalization':'No genuine endpoint proved; no Lean theorem, replay, or axiom audit claimed','trust_limits':'Dependencies kept read-only; prebuilt oleans unaudited; no full upstream rebuild/source-to-olean attestation','limits':'diagnostics each taskset at most 2 CPUs, RLIMIT_AS 6 GiB and RLIMIT_CPU 110/120 seconds, timeout 140 seconds; HTTP and small provenance scripts lightweight, not RSS monitored'}
(D/'environment.json').write_text(json.dumps(env,indent=2)+'\n')
