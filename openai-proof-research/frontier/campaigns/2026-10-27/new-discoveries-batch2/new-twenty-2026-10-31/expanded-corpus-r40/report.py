import json,pathlib,hashlib,subprocess,datetime
L=pathlib.Path(__file__).resolve().parent;B=L.parent.parent;R=json.load(open(L/'records.json'));H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
context={}
for p in [pathlib.Path('openai-proof-research/AGENTS.md'),B/'AGENTS.md',L.parent/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',L.parent/'ledger.json']:
 b=p.read_bytes();entry={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
 if p.suffix=='.json':
  d=json.loads(b);entry['top_level_keys']=list(d);entry['accepted']=d.get('accepted',[]);entry['other_disposition_context']={k:v for k,v in d.items() if any(t in k.lower() for t in ['reject','exclu','protect','hold','famil','count'])}
 context[str(p)]=entry
(L/'inherited-context.json').write_text(json.dumps(context,indent=2))
# Target-specific reasons for routes not selected for primary-body work.
gaps={
347678:'Dichromatic number>=3 must force a subdivision of some bioriented cycle; no all-digraph structural mechanism. Source-family match r39 concerns different reserved IDs, not exclusion of this literal claim.',
347686:'Design D is defined outside the record. No primary design construction or all-prime-power dual-code distance proof recovered; cannot substitute a generic projective-plane code.',
347709:'Depends on dg flag Hilbert scheme adjunctions and Rouquier complexes; no coherent-category full isomorphism construction or feasible Lean bridge.',
347723:'Equation8.0.1 and precise breaking/pointwise-versus-norm definitions require primary source. No PDE continuation theorem or sufficient breaking criterion established.',
347730:'Asymptotic minimization for every k>ell requires precise quasi-star/quasi-clique and path-copy conventions; no density-regime extremal comparison.',
347768:'Large-outdegree forcing of all fixed subdivisions needs a structural preservation theorem, not repeated application of the original F threshold.',
347798:'No general k-connectivity to monochromatic-cut partition inequality. Known ranges in record do not settle all k.',
347816:'Classical girth extremal construction for all l; no exact all-l mechanism. Small-n wording objections are ineligible.',
347822:'Matching pattern containment and rank3 intervals require primary definitions; no extremal Mobius proof or certified counterexample.',
347860:'Fine cycle/surface and isometric filling definitions not newly body-reviewed. Prior source alias historical-depth-r21 is a source-family match requiring reconciliation, not novelty clearance.',
347863:'Need retain linear minimum degree and O(D) injective colors simultaneously for every regular r-graph; edge-count-only sparsification does not bridge.',
347868:'Replacement conjecture includes threshold delta>=ceil(3k/2)-1 and additive O(1); no unbounded connected counterexample family or diameter proof.',
347876:'Need chi_s bounded as a function of clique number under fixed induced K1,t exclusion; no all-size coloring mechanism proved.',
347877:'Need chi_s bounded for every fixed tree T with induced C4 exclusion; no tree induction and coloring extension.',
347901:'Need minimal Ramsey construction realizing the exact minimum degree for every connected triangle-free H; no signal-sender/minimality construction.',
347910:'Asymptotic inverse-closed sum-free optimum over all finite fields; a finite-field instance cannot refute o(1). No constant-density infinite counterexample family.',
347940:'Typicality and iterated singularity complexity are source-dependent dynamical definitions; no subexpansion-rate estimate.',
347978:'Friends-and-strangers d_r,r needs exact quantifiers and exceptional small r convention. No general connectivity construction or bound.',
347981:'Largest small even polygon optimizer symmetry for all even n>=6; no global optimality or asymmetric maximizing witness.',
348004:'Density modifies the connection; ordinary Levi-Civita holonomy does not answer the source question. Weighted connection and all-n curvature closure not recovered.',
348035:'Sufficiently large face degree and face-overlap threshold are asymptotic; no cyclic coloring extension theorem.',
348036:'Subdivision cyclic coloring bound requires all subdivisions of all simple3-connected plane graphs; no reusable coloring of core and subdivided edges.',
348104:'Superbridge index3 classification requires global embedding invariants, not a computed upper bound for a chosen embedding.',
348148:'No full subcubic injective edge-coloring extension or literal counterexample. Source definition of injective conflict must be recovered.',
348166:'SY class independence needs source torsor and Brauer obstruction definitions in characteristic2; no full comparison theorem.',
348242:'Tensor spectral-radius extremizer among planar3-uniform hypergraphs for sufficiently large n; no shadow-to-hypergraph maximality proof.',
348245:'Need lower bound for minimal bad domains under connected sum; source upper construction alone cannot prove additivity.',
348276:'BV section uniqueness/equidistribution from a q-harmonic limit requires primary affine-bundle and lamination quantifiers. No analytic uniqueness proof.',
348278:'Local obstruction asymptotics fixed p all(0,1); small singular matrices cannot settle a relative o(1) probability assertion.',
348300:'Need exact source object (surface versus arbitrary complex) before full scope. No extremal homeomorphic embedding construction.',
348336:'geomgon is undefined in the record and source-dependent. No genus/field-wide gonality bridge; no domain correction claimed.',
348348:'Wide-generated semibrick-pair category rank condition needs actual algebraic completion proof, no rank-only finite diagnostic.',
348361:'Quantifier over triangle centers and degeneracy conventions require source. No complete ellipse-only-if classification; arbitrary invented centers would widen scope.'}
rows={}
receipts={}
for f in L.glob('source-receipts*.json'):receipts.update(json.load(open(f)))
for k,v in R.items():
 i=int(k);d=v['record'];rows[k]={'mathdb_id':i,'title':d['title'],'literal_statement':d['statement'],'provenance':v['provenance'],'source_url_from_record':d['source_url'],'metadata_preliminary':True,'inherited_matches':[], 'review_depth':{'new_literal_record_read':True,'new_primary_definitions_read':False,'new_primary_proof_body_read':False,'inherited_review_not_claimed_as_new':True},'outcome':'PARK_LITERAL_ONLY','reason':gaps.get(i,''),'remaining_lemmas':gaps.get(i,''),'credit':0,'lean_endpoint':None}
 for p in ['history-id-paths.txt','history-title-source-matches.txt']:rows[k]['historical_search_evidence']= ['history-matches.json','history-title-source-matches.txt']
for i,sources,outcome,why,remaining in [
(347711,['2008.11448'],'HOLD_STRUCTURAL_GAP','Read source definitions and Conjecture1; dual response-map formulation investigated. Optimized-cardinality concavity does not follow from submodularity.','Prove concavity of exact optimal response-map profile for every n,m, or find exact nonconcave optimal profile with upper bounds.'),
(347712,['2008.11448'],'CANDIDATE_ORDINARY_REFUTATION_LEAN_IN_PROGRESS','Explicit n5 cyclic Latin strategy field290 and competitor field302; actual magneticities checked. See PROOF-ATTEMPTS.md.','Finish kernel literal refutation, extracted strict replay and all-declaration audit; independent significance/fidelity review and prior-art clearance remain.'),
(347913,['2009.04510','published-brosch','polak'],'HOLD_ORDINARY_PROOF_NO_LEAN','Full ordinary moment identity proof of literal convexity, with independent exact rational diagnostics. No full Lean semantic bridges.','Certified joint-survival moment expansion, chamber integrals with repeated labels, integrability and convexity expectation in Lean; contemporary prior art.'),
(348181,['2010.01655'],'HOLD_PRIMARY_PARTIAL_PROOF_GAP','Conjecture4.21 and Lemmas4.16–4.20 proof bodies read. The difficult induction subcase remains.','All-coefficient incompleteness-to-root bound in Subcase2, no finite root sweep suffices.'),
(348265,['2010.05521','published-fibonacci'],'EXCLUDE_ROUTINE_EXPLICIT_BRIDGE','Direct positive-support extremal monomial calculation in source Eq41 gives exact threshold; full bridge in PROOF-ATTEMPTS.md.','None for routine bridge; no discovery credit or formalization.'),
(348251,['toughness'],'EXCLUDE_KNOWN_PRIMARY_PROOF','Source Theorem1 proves precisely t(G)>=d/lambda-1; full proof including both component partition claims and mixing-bound conclusion read.','No new theorem to formalize.'),
(348053,['kalai'],'EXCLUDE_KNOWN_REPORTED_IN_PRIMARY','Source introduction expressly credits Bonamy–Charbit–Thomasse for exact chromatic conjecture and Scott–Seymour generalization; original cited proof body not downloaded/read. Exclusion at known-result lead level, not independent verification.','Read original BCT theorem/proof if independent proof verification is needed; no discovery claim.')]:
 r=rows[str(i)];r.update(outcome=outcome,reason=why,remaining_lemmas=remaining);r['sources']={s:receipts[s] for s in sources};r['review_depth'].update(new_primary_definitions_read=True,new_primary_proof_body_read=i not in [348053],primary_proof_scope='Selected relevant source sections, not entire manuscripts; see PROOF-ATTEMPTS.md')
rows['347678']['inherited_matches']=[{'path':'../expanded-corpus-r39/results.json','kind':'same source2008.09888, different exact targets; no old exclusion inferred'}]
rows['347860']['inherited_matches']=[{'path':'../historical-depth-r21/results.json','kind':'same source2009.02415; actual prior context must be read before renewed investment'}]
assert len(rows)==40
(L/'results.json').write_text(json.dumps(rows,indent=2))
print('wrote',len(rows),'results')

# Preserve completed certification when rebuilding the report after replay.
if (L/'strict-extracted-receipt.json').exists():
 rows['347712'].update(outcome='CANDIDATE_FULL_LITERAL_LEAN_REFUTATION_PENDING_INDEPENDENT_REVIEW',lean_endpoint='MathDB347712.source_refutation : ¬ MathDB347712.SourceClaim',formal_receipt='strict-extracted-receipt.json',packet='lean-packet.zip',local_declaration_audit_total=22,credit=0)
 rows['348265']['review_depth']['new_primary_proof_body_read']=False
 for row in rows.values():row['prior_art_cleared']=False
 (L/'results.json').write_text(json.dumps(rows,indent=2))
