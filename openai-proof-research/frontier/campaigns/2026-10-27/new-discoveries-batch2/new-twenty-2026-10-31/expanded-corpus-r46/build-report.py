import pathlib,json,hashlib,re,datetime,subprocess,platform
p=pathlib.Path(__file__).resolve().parent;b=p.parent.parent;sha=lambda x:hashlib.sha256(x).hexdigest(); r=json.loads((p/'reservation.json').read_text()); prov=json.loads((p/'literal-provenance.json').read_text());ctx={}
for f in [b.parent.parent.parent/'ledger.json',b/'ledger.json',b/'prior-campaign-context.json',p.parent/'ledger.json']:
 if not f.exists():continue
 d=json.loads(f.read_text());ctx[str(f)]={'sha256':sha(f.read_bytes()),'counts':{k:v for k,v in d.items() if 'count' in k},'accepted':d.get('accepted',[]),'exclusions_and_holds':{k:v for k,v in d.items() if any(w in k.lower() for w in ['reject','exclud','protect','held'])}}
(p/'inherited-context.json').write_text(json.dumps(ctx,indent=2,ensure_ascii=False)+'\n')
notes={
352705:'Source concluding Conjecture 4.2 literally repeats B_2 although its construction depends on t. The left side is independent of t, so varying t gives a wording contradiction, not a qualifying source-scope discovery. No integer-rounding refutation claimed.',
352725:'Literal status note only says proved in type A. This is not a full-Weyl-group exclusion. Recover p-canonical basis and full p-cell hypotheses before an exact finite computation.',
352768:'Need epsilon depending on fixed even k, not on n. Complete graphs give the usual k/(k+2) obstruction for odd k; changing parity or k=0 would be an endpoint route, not a solution. Primary source unread.',
352779:'Exact source already reports two counterexample families; Conjecture AAA and Theorem 4 proof portions inspected. Stop discovery route as known refutation, without claiming independent verification of every spectral calculation.',
352818:'Large-girth quantifier rules out using a fixed low-girth graph; imbalance remainder is part of the claim. Need a family of arbitrarily large girth or a uniform coloring theorem. Primary definitions unread.',
352853:'Full alpha=2 clique-cover bound has no discovered mechanism. Complement triangle-free reformulation alone supplies no edge cover with n cliques. Primary body unread.',
352890:'Metadata/title appears in older pi-analysis source inventory, not a technical disposition. Stark unit and ray class field choices must be recovered; no generic SIC example resolves them. Primary body unread.',
352940:'Period equality/isomorphism wording cannot safely be tested without exact mirror class and equivalences. Hold for primary-scope recovery, no arbitrary mutations used as refutations.',
352987:'Asymptotic bound for all d,k; finite small configurations do not refute big-O. Need superexponent family. Source definitions unread.',
352988:'Must recover whether k counts vertices or simplex dimension; no indexing correction is a discovery. Asymptotic exponent needs unbounded family. Primary body unread.',
353016:'Need cubic girth>=6 graph with independent domination >n/3, including an exact domination lower bound. No witness found or graph sweep performed.',
353025:'Gaussian coordinates and Stiefel rank/dimension absent from paraphrase. Scaling sigma may reduce the optimization but does not prove optimality at P=0. Primary source unread.',
353049:'Sustained source-fidelity/closure route; see ATTEMPTS.md. Exact finite-grid closure checks are not global extremality. No endpoint.',
353091:'Need planar girth>=6 graph with no odd four-coloring, or full discharging theorem. Trees/cycles do not decide full claim. Primary proof unread.',
353173:'Component diameter asymptotics cannot be refuted by one fixed graph or disconnectedness. No uniform superquadratic family or quadratic routing algorithm obtained.',
353193:'Epsilon quantified in (0,8/5]; boundary effects must be source-checked. No selected finite graph/no-coloring certificate. Primary source unread.',
353200:'Optimal control activity depends on cost, admissibility and dual terminal conditions; none reconstructed from the literal text. Source gap held, no geometric analogy claimed as proof.',
353205:'Anosov type and scattering data definitions indispensable. Nontrapping/simple examples do not settle this class. Primary body unread.',
353237:'Unquantified Errors and inherited Psi_Phi require original analytic normalization. No formalizable literal endpoint recovered. Primary body unread.',
353241:'Sustained exact product route with correlation bound, boundary analysis and two distinct MILP models; see ATTEMPTS.md. No all-parameter bridge and no counterexample.',
353263:'Inherited OpenAI catalogue explicitly lists prior ETH refutation (entry378). Stop this route under inherited known-result protection; no full proof-body read or independent verification newly claimed.',
353277:'Symmetrizing f need not preserve nonlinear convolution M. Need source-defined admissible pairs and attainment; no Jensen shortcut accepted. Primary body unread.',
353285:'Paraphrase explicitly equivalent to Ryser; zeon notation alone cannot make a new result. No ordinary full Ryser solution or source-body review.',
353341:'Later primary Bell et al arXiv2406.00243 Theorem1.5 explicitly proves the same Conjecture4.3; definitions and main lower-bound/bridge proof bodies read. Known full-scope result, no formalization for credit.',
353406:'Need full directed branching decomposition with fractional-arboricity and indegree restrictions. Undirected Nine Dragon Tree result is not a complete bridge. Primary source unread.',
353407:'Realization requires effective topological action for all finite subgroups; algebraic splitting alone is insufficient. No primary-body investigation.',
353427:'Literal solved annotation describes many instances, not the universal forcing-absoluteness claim. No universal solved exclusion made; primary source unread.',
353471:'Full planar dichromatic bound is broad; no graph witness or acyclic two-color theorem. Protected-family ledger matches not found by exact ID/title apart from inventory.',
353484:'Need exact dispersion definition and Perron normalization before comparing kites. No spectral diagnostic on this unrelated dispersion claim performed.',
353488:'Refuted label alone does not identify counterexample scope. Hold for source statement and weight-domain proof body; no known-result exclusion newly certified.',
353489:'Known k=5 alone would be parameter instance. Need all k>=5 or a violating length with rigorous inducibility lower bound. Primary body unread.',
353506:'Literal record cites Corwin-Hammond/Pimentel/Flores prior proofs. Stop as prior-resolution lead, not a new body-verified exclusion or new formalization.',
353517:'Sustained source-original partition route; misleading refuted annotation corrected only administratively. Actual Conjecture12/Drury Conjecture1 remain distinct from known prohibited-diagram witnesses. See ATTEMPTS.md; no endpoint.',
353519:'Primary Conjecture2.7 is the revised k-notin{2,4} assertion; source refutation text targets older Levenshtein assertion. Lemma2.3, Proposition2.5 and Theorem2.8 proof read. No revised-conjecture refutation claimed; k=1 endpoint not used.',
353537:'Conjunction of proper open conflict-free and proper closed unique-maximum class maxima. No identification with ordinary coloring accepted. Primary definitions unread.',
353540:'Inventory title match only. Exact (a,b)-bipartite strong-coloring bound still requires full degree-sensitive argument; balanced special cases not credited. Primary body unread.',
353590:'Source distinguishes known unweighted Theorem1 from weighted Krenn-Gu Conjecture1/appendix Conjecture2. Weighted cancellation/monochromatic-state definitions indispensable. Known unweighted statement is not claimed to resolve primary weighted question. Hold fidelity, no counterexample.',
353617:'Fixed n,epsilon,I bound; dimension<=3 result not full scope. No algebraic-geometric bridge or primary-body read.',
353618:'DCC coefficient set and codimension quantifier stronger than finite-coefficient/positive-volume special cases. No full mechanism; primary body unread.',
353619:'Need exact Q-linear divisibility convention and K-semistability restriction; arbitrary Fano examples do not refute it. Primary source unread.'}
primary={352705:('2111.11162','concluding construction and Conjectures4.1-4.2','selected_statement_and_construction'),352779:('2111.15303','Conjecture AAA; Lemma1 proof; Theorem4 and Riemann-sum proof portions','selected_definitions_and_proof_portions'),353049:('2112.12716','Section3 Lemma15; extension convention; Conjecture16; Lemmas37/50 and selected extremality proof','selected_definitions_and_proof_bodies'),353241:('2201.03865','Definition3, Conjecture2; Theorem11 proof and Harris-Kleitman/IU proof','definitions_and_selected_proof_bodies'),353341:('2201.08464','Definitions3.1/4.1; Conjecture4.3; Proposition4.7 proof; later2406.00243 Theorem1.5, Proposition2.1 and1.8 proof bodies','original_and_later_primary_proof_bodies'),353517:('2202.01867','Conjecture12 and known counterexample discussion; original Drury2018 Sections2-4 including Fourier/permanental-minor bridge','original_and_survey_selected_bodies'),353519:('2202.01948','Definition/monotonicity; Proposition2.5, Conjecture2.7, Theorem2.8 proof','selected_definitions_and_proof_body'),353590:('2202.05562','Theorem1; PMValid definition; weighted Conjecture1 and appendix definitions','definitions_and_statements_only')}
history=(p/'history-filtered.txt').read_text().splitlines();out={}
for row in r['rows']:
 i=row['mathdb_id'];v=prov[str(i)];matches=[s for s in history if re.search(r'(?<![0-9a-f])'+str(i)+r'(?![0-9a-f])',s.split(':',2)[-1]) or row['title'].lower() in s.split(':',2)[-1].lower()]
 outcome='HOLD_literal_only_no_full_mechanism'
 if i in [353049,353241,353517]:outcome='PARKED_sustained_attempt_no_endpoint'
 if i in [352779,353341]:outcome='EXCLUDE_known_primary_resolution'
 if i==353263:outcome='STOP_inherited_registry_prior_resolution'
 if i in [352705,353519,353590]:outcome='HOLD_source_scope_or_status_mismatch'
 out[str(i)]={'mathdb_id':i,'title':row['title'],'literal_statement':v['record']['statement'],'provenance':{k:z for k,z in v.items() if k!='record'},'raw_file':f'raw/{i}.jsonl','source_url':v['record']['source_url'],'outcome':outcome,'discovery_credit':0,'self_accepted':False,'new_review_depth':primary.get(i,(None,None,'literal_statement_only'))[2],'primary_sections_read':primary.get(i,(None,None,None))[1],'primary_receipt':f'sources/{primary[i][0]}-receipt.json' if i in primary else None,'inherited_matches':matches,'inherited_match_interpretation':'Administrative inventory/reservation matches are not technical review; ETH catalogue prior-resolution match is substantive. No unindexed old exclusion located in this bounded exact-ID/title search. Long JSON lines were capped; this is not an exhaustive semantic history audit.','assessment':notes[i],'lean_endpoint':None,'remaining_requirement':'Full literal proof/refutation, semantic bridges, literature/fidelity review and Lean certification remain absent.'}
assert len(out)==40 and set(map(int,out))==set(r['ids']);(p/'results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
# Current registry evidence, preserving incomplete Omega baseline explicitly.
reg={}
for name in ['openai','omega']:
 d=json.loads((p/'sources'/f'{name}-head.json').read_text());reg[name]={'head':d['sha'],'receipt':f'sources/{name}-head-receipt.json','head_file_changed_paths':[x['filename'] for x in d.get('files',[])],'coverage':'HEAD commit receipt only; no completeness inferred from changed files'}
f=p.parent/'fresh-corpus-r10/sources/registry-preprints.json';d=json.loads(f.read_text());reg['reused_complete_preprints']={'file':str(f),'sha256':sha(f.read_bytes()),'tree_sha':d['sha'],'truncated':d.get('truncated'), 'hits':[x['path'] for x in d['tree'] if re.search('exponential-time|toric|schur|down-sets|square-rich|permanental',x['path'],re.I)]};assert not d.get('truncated');reg['omega_limitation']='Current head differs from supplied9abc86d1; incomplete historical baseline remains incomplete. No full Omega nonfinding or clearance.';(p/'registry-review.json').write_text(json.dumps(reg,indent=2)+'\n')
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean';env={'lean_version':subprocess.check_output([lean,'--version'],text=True).strip(),'lean_binary_sha256':sha(pathlib.Path(lean).read_bytes()),'mathlib_requested_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','mathlib_root':'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib','python':platform.python_version(),'no_lean_endpoint':True,'trust_limit':'Cached upstream oleans not rebuilt or attested. No local Lean theorem and hence no endpoint replay or axiom audit claimed.'};(p/'environment.json').write_text(json.dumps(env,indent=2)+'\n')
print('40 dispositions written; primary-depth records',len(primary),'context files',len(ctx))
