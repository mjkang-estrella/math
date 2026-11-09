import pathlib,json,hashlib,datetime
w=pathlib.Path(__file__).resolve().parent
r=json.loads((w/'reservation.json').read_text()); prov={x['id']:x for x in json.loads((w/'provenance.json').read_text())}
notes={
349393:'Need source definitions of extra dimension, chart algebra A_lambda and standard torus action; no equivariant Plucker local-model proof attempted.',
349395:'Need source tangent/embedded-dimension convention and field hypotheses. Minimal excess six is not certified from cached computations; no dimension theorem proved.',
349405:'Need flag class, pullback convention, Picard-number scope and source upper-bound theorem; no birational flag construction attempted.',
349425:'Exclude: pre-existing public tW5 counterexample; actual source component theorem and public counterexample body read. See ATTEMPTS.md.',
349503:'Need source subfield r-divisibility/r|[Fq:Fp] convention and Cayley adjacency. Character-sum/maximality route unattempted; missing convention is not a counterexample.',
349536:'Cached bound raises parity and edgeless-forest questions. Recover source rounding/parity hypotheses before any witness; no endpoint correction proposed.',
349548:'Need source lower-order index range, non-isotriviality and averaging existence; omitting leading p term in a paraphrase is not a discovery. Same bias family as 349629/349996.',
349579:'Ambient corner-free domain and exact asymptotic quantifiers not recovered from primary body; no density construction.',
349585:'Literal displayed claim omits star-free condition stated in surrounding prose. Source-induced K1,n-free scope controls; no unrestricted-graph surrogate construction.',
349588:'Primary older version containing LR statement must be located and compared with Kostka paper. No Hilbert-basis/decomposability proof attempted.',
349594:'Need epsilon/n0 formulation behind (3/4+o(1))n and current resolution body. No extremal construction or full-scope proof.',
349612:'Need alpha(n), dimension-dependent C and asymptotic probability quantifiers; no random-geometric Hamiltonicity proof.',
349618:'Need objective (area/perimeter), free disk placement and source optimality quantifiers. Literal smallest triangle ambiguous; no geometric counterexample certified.',
349620:'Need centered-hexagonal range, fixed disk radius and optimization objective; n=1/empty-set anomaly would be an excluded endpoint correction.',
349629:'Same negative-bias family as 349548/349996. Need precise lower-order expansion and source exclusions; no arithmetic family evaluated.',
349648:'Exclude as routine full-scope Fejer-Jackson consequence with explicit derivative/rescaling/reflection bridge in ATTEMPTS.md; primary theorem/proof read.',
349650:'Need actual graph G_t definition, feasible k,t,n range and switching/isomorphism convention. No signed spectral comparison proved.',
349674:'Exclude exact prior proof: 2305.03370 Theorem3, full proof pp10-12 read, matches 2102.04126 Conjecture1.',
349680:'Cached source claims a complete extremal solution; need actual theorem/proof before known-resolution exclusion. No inference of open status from record label.',
349709:'Need intersection-density normalization and prime distinctness; p=q and p=2 endpoint issues are not eligible discoveries. No permutation-group search.',
349713:'Strongest remaining route: source recurrence/quasipolynomial and published conjecture read; Pell and residue-line mechanisms developed; uniform square-product residue lemma and full Lean bridges remain. See ATTEMPTS.md.',
349739:'Need list-coloring/genus definition and primary source lower-bound equality bridge; no choosability proof.',
349740:'Need genus/chromatic feasible range, exact jump maximum definition and all-r inequalities; no unimodality proof.',
349754:'Need PDE, p-side/neighborhood, nodal energy and symmetry conventions from source; no PDE argument.',
349765:'Inherited family match under 345998 in expanded-corpus-r38: known-resolution lead only, body not verified there or here. Retain hold; do not re-invest or claim a new exclusion proof.',
349771:'Corrupted se=3/poset notation requires source recovery; induced grid embedding and matrix containment conventions unresolved. No nearby pattern theorem claimed.',
349785:'Need generalized cutset/gap threshold and allocation/valuation definitions, including boundary ownership. No topological fair-division proof.',
349816:'Corrupted comparison symbols and j=0 domain need source recovery. No j=0 wording counterexample and no Grassmann eigenvalue computation.',
349822:'Need exact fixed surface class, covector quotient, chaotic-section definition and dimension theorem; no geometric-measure proof.',
349838:'Method-dependent future direction lacks exact group class and construction quantifiers. Need actual source problem before claiming an existence theorem.',
349848:'Same low-sum forest family as 349536; source parity/rounding and Delta=0/1 conventions not recovered. No duplicate family credit.',
349868:'Cached references say refuted, status says open; need actual source/published body before prior-resolution assertion. No surface-area minimization proof.',
349904:'Need actual wave maximal theorem, representative/trace conventions and higher-dimensional endpoint range; no harmonic-analysis proof.',
349912:'Source oriented graph must exclude opposite pairs as well as loops; defective shorthand cannot create a counterexample. No asymptotic cycle construction.',
349952:'Need exact stable ensemble, tail scaling and point-process limiting quantifiers; heuristic considerably larger is insufficient formal scope.',
349987:'Need source field hypotheses, type X1111 and arithmetic versus geometric Picard-rank convention; no rationality witness.',
349996:'Duplicate bias family 349548/349629; source definition/averaging limit gaps remain. No separate credit.',
350041:'Need exact partial4-tree and 2-connected hypotheses plus source longest-cycle construction; no transversal enumeration or proof.',
350054:'Need nontriviality and extremal inducibility quantifiers for fractalizer. Smallest-asymmetric-order wording is not a qualifying result; no flag-algebra proof.',
350141:'Need source Borsuk-number/covering bridge and general norm scope; no convex-cover theorem or finite certificate.'}
src={349425:['2101.06180.pdf','complementation-public.html'],349648:['2102.02979.pdf','fejer-body.pdf'],349674:['2102.04126.pdf','cheb-later.pdf'],349713:['2102.05352.pdf','partition-published.pdf']}
out={}
for row in r['rows']:
 k=int(row['mathdb_id']); x=json.loads((w/'raw'/f'{k}.jsonl').read_text());p=prov[k]
 z={'mathdb_id':k,'title':x['title'],'canonical_url':x['canonical_url'],'source_url':x['source_url'],'literal_statement':x['statement'],'provenance':{'chunk':p['chunk'],'one_based_line':p['line'],'chunk_sha256':p['chunk_sha256'],'raw_line_sha256':p['raw_sha256'],'statement_utf8_sha256':hashlib.sha256(x['statement'].encode()).hexdigest(),'raw_copy':f'raw/{k}.jsonl','newline_preserved':(w/'raw'/f'{k}.jsonl').read_bytes().endswith(b'\n')},'outcome':'parked_primary_definitions_not_reviewed','accepted_credit':0,'actual_review_depth':'cached_literal_statement_read; bounded_ID_title_source_alias_history_search','new_primary_body_review':False,'inherited_matches':[],'assessment':notes[k],'sources_reviewed':[],'lean_endpoint':None,'formal_status':'No Lean theorem or packet; no strict replay/axiom-audit claim.','history_search':'history-all-exact.txt; history-title-*.txt; history-mechanism.txt','history_limit':'Search covers selected report/result/ledger files, excludes originals/legacy-aliases/corpus/tag trees; no global nonreview assertion. Administrative current reservation matches do not establish technical review.','remaining_gate':'Recover exact primary definitions/quantifiers and theorem bodies, then rigorous full-scope ordinary and literal Lean proof; live prior-art/subsumption and independent review.'}
 if k in src:
  z.update(new_primary_body_review=True,actual_review_depth='new_primary_definitions_and_selected_theorem_proof_bodies_read; scope and limits in ATTEMPTS.md',attempt_file='ATTEMPTS.md')
  z['sources_reviewed']=[{'file':'sources/'+f,'sha256':hashlib.sha256((w/'sources'/f).read_bytes()).hexdigest(),'receipt':'source-receipts*.json'} for f in src[k]]
 if k==349425:z['outcome']='excluded_prior_public_counterexample_body';z['remaining_gate']='No qualification investment: already public full-scope counterexample.'
 if k==349648:z['outcome']='excluded_classical_routine_full_scope_bridge';z['remaining_gate']='No formalization required for known/routine exclusion.'
 if k==349674:z['outcome']='excluded_exact_later_primary_proof';z['remaining_gate']='No qualification investment: exact prior theorem/proof.'
 if k==349713:z['outcome']='parked_sustained_Pell_and_residue_route';z['remaining_gate']='Uniform compatible residue lemma for square ab, complete nonsquare Pell orbit proof and all Lean semantic bridges. Prior-art search is bounded and incomplete.';z['rank_among_surviving_routes']=1
 if k==349765:z['outcome']='inherited_family_hold';z['inherited_matches']=[{'mathdb_id':345998,'path':str(w.parent/'expanded-corpus-r38/results.json'),'type':'same_1-2-3_family; known-resolution lead; unread_primary_body','action':'Retain hold, no new investigation.'}]
 if k in [349536,349848]:z['within_assignment_family']=[349536,349848]
 if k in [349548,349629,349996]:z['within_assignment_family']=[349548,349629,349996]
 out[str(k)]=z
assert len(out)==40 and set(map(int,out))==set(r['ids'])
(w/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
