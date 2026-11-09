import json,pathlib,hashlib,datetime,re,subprocess
L=pathlib.Path(__file__).resolve().parent;B=L.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();ex=json.loads((L/'extracted.json').read_text());res={}
notes={
341830:'Quantification over classes and precompact expansions requires the actual language and hereditary/amalgamation hypotheses. No source body read; no pathological-class counterexample accepted.',
341872:'All fixed r>k>=2,e>=3 asymptotics. A small hypergraph or one exponent does not settle both asymptotic bounds. No primary-body or current-resolution clearance.',
341877:'Uniform ambient-manifold translation bound requires arc-complex and fiber-monodromy semantics. No primary-body review or feasible literal Lean bridge identified.',
341931:'Requires exact total-label separation and label indexing. p=1 would contain total coloring; no labeling convention correction or isolated special case selected.',
341988:'The four extremal-monomial sets and stability test configurations are not defined in the cached statement. No source body recovered; no adjacent singularity question substituted.',
342004:'Regularity measure definition and asymptotic constants need primary recovery. Sunflower/compression results are leads only, not a body-verified exclusion.',
342014:'Requires source extremizer D_(n,r,s), ordered distances and biconnectivity scope. No primary definitions reviewed; no finite digraph search run.',
342015:'Shares source extremizer family with 342014; neither is counted as a new family. No primary-body review.',
342034:'Literal intersection is convex, suggesting a transcription error relative to union homology; no source read, so no correction or source-only substitute claimed.',
342042:'Both full ERK and k_on=0 networks, positive and stable maxima, require exact reaction system and stability definition. No numerical endpoint attempted.',
342055:'Unchaining and symplectic Kodaira dimension require substantial topology; no primary body or concrete full-scope Lean route.',
342091:'Largest affine subspace and admissible variety hypotheses may be missing from paraphrase. No arbitrary-variety counterexample promoted without primary scope.',
342095:'Orientation posets, area sequences and chain partitions need primary definitions. LLT literature is a possible prior-art lead, not a verified resolution.',
342109:'Non-discrete locally compact Abelian groups; malformed S(G) notation and exact M_00 definition require recovery. No primary body read.',
342111:'Incidence-stratum definition missing; all k embedding-dimension equality is not reducible to a small k computation without bridges.',
342159:'Need actual J_e and o-monomial exponent equivalence modulo q-1. No exponent-representative correction counts; no source read.',
342199:'Generic complex critical count for MA(1), not numerical real stationary points. Exact covariance parametrization/degree bridges unread.',
342235:'A limit comparison of two extremal graph invariants. Neither individual graph examples nor bounded sweeps prove it. Primary body unread.',
342237:'Full Cerny bound for every synchronizing automaton. No source-body review or tractable full-scope proof selected.',
342264:'All Fano pairs and all tuple lengths; no definitions of log invariants recovered. No source-only or restricted-pair claim.',
342272:'Uniform fractional matching threshold limsup for all ell,d. No primary-body or modern resolution check; no finite LP result mistaken for asymptotic endpoint.',
342331:'Subdivision of all even-cycle unions, balanced bipartite degree condition. No primary-body review; small cycle instances insufficient.',
342354:'Normal 5-edge-coloring of every bridgeless cubic graph. No source-body check or full certificate mechanism identified.',
342396:'Exponential upper bound on arbitrary pairwise reversing families. No bounded permutation enumeration would establish the claimed growth.',
342426:'Quantum A-polynomial and actual normalized knot series definitions absent. Source metadata solved cue concerns q-holonomicity, not verified as this endpoint.',
342499:'Coefficient-scaling sign in displayed inequality is suspect; source unread. Scaling correction is not treated as discovery.',
342560:'Satellite/quasi-alternating classifications require source topology and current bodies; no concrete counterexample mechanism selected.',
342583:'Multiplicity of affine hyperplane covers of all cubes; paraphrase has contradictory ranges. No endpoint correction or bounded cube check counted.',
342675:'Genericity of exact Jacobian (J2) depends on its polynomial system and parameter space. Source body unread.',
342734:'Garbled parameter notation and Hatcher status cue require source recovery. No invariance classification or known-result claim inferred.',
342755:'Intersection of kernels over all dimensions and smooth potentials. Would need universal Lie/Poisson semantic bridge, not just low-degree identities.',
342773:'Minimal-model definition absent; metadata refutation cue not checked in actual body, so no exclusion based on that cue.',
342791:'All 3-connected cubic planar graphs and all qualifying k; no primary-body or current sharp-bound verification. No finite examples settle it.'}
primary={341918:('cycles','known_source_theorem','Actual Conjecture1.1, Theorem1.3, complete main proof read; H=odd cycle critical-edge bridge proves exact target.'),341944:('determinant','hold_source_ambiguity','Definitions1.1-1.8, row-partition inequality, full Theorem7.1 proof, Conjecture7.2 and consequence read. Natural interpretation refuted arithmetically but source subscripts undefined.'),342350:('irredundance','parked_hard_full_scope_gap','Definitions, Conjecture1.1, Theorems1.2/1.3, full polynomial proof and selected stability application read; 37 exceptions remain, not a full proof.'),342351:('irredundance','parked_weighted_clone_gap','Conjecture1.2 and same primary proofs read. Twin reduction and nonuniform-weight obstruction investigated; no full inequality.'),342431:('dominator','excluded_routine_or_definition_correction','Definition1, Theorem1, Lemmas1/2/5/6 and proofs, Conjecture1 read. Explicit source path theorem bridge contradicts formula.'),342432:('dominator','excluded_routine_or_definition_correction','Same primary and Conjecture2 read; directed path and anti-arborescence singleton argument give routine obstruction.'),342200:('forcing','parked_general_realization_gap','Exact minimal-k drawing definition, Conjecture6, Proposition28 and Theorem3 proof bodies, Remark29 read. General forcing-chain embedding missing.')}
fr={r['name']:r for r in json.loads((L/'fetch-receipts.json').read_text())}
hist=(L/'history-search.txt').read_text().splitlines();old=(L/'older-history-search.txt').read_text().splitlines()
for k,v in ex.items():
 i=int(k);d=v['record'];p=primary.get(i)
 r={'mathdb_id':i,'title':d['title'],'literal_statement':d['statement'],'canonical_url':d['canonical_url'],'source_url':d['source_url'],'provenance':v['provenance'],'raw_file':f'raw/{k}.jsonl','inherited_matches':[],'history_check':{'scope':'Batch/campaign markdown, results and ledgers; previous campaign same file classes; ID/title bounded searches. Metadata reservations and numeric substrings are not substantive history.','substantive_match_found':False,'logs':['history-search.txt','older-history-search.txt']},'new_review_depth':'literal_cached_statement_only','primary_body_read':False,'outcome':'parked_literal_only_unresolved','reason':notes.get(i,''),'attempts_file':'ATTEMPTS.md','lean_endpoint':None,'discovery_credit':0,'root_acceptance_required':True}
 matches=[x for x in hist+old if re.search(r'\b'+k+r'\b',x) or d['title'].lower() in x.lower()]
 r['history_check']['matching_lines']=matches
 if p:
  name,outcome,reason=p;r.update(new_review_depth='primary_definitions_and_selected_theorem_proof_bodies',primary_body_read=True,outcome=outcome,reason=reason,primary_source_receipt=fr[name],primary_text_file=f'sources/{name}.txt')
 res[k]=r
assert len(res)==40 and set(res)==set(map(str,json.loads((L/'reservation.json').read_text())['ids']))
(L/'results.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
# Verify all manifest-bound normalized chunks and reservation immutable indexes.
inv=B/'lanes/pi-mathdb-full-corpus-inventory-r301';man=json.loads((inv/'manifest.json').read_text());chunks=[]
for f in man['files']:
 if f['path'].startswith('corpus/mathdb-normalized-chunk-'):
  actual=sha((inv/f['path']).read_bytes());assert actual==f['sha256'];chunks.append({'path':f['path'],'sha256':actual})
assert len(chunks)==20
r=json.loads((L/'reservation.json').read_text());inputs=[]
for s,h in r['input_hashes'].items():
 p=pathlib.Path(s);a=sha(p.read_bytes());mutable=p==L.parent/'ledger.json';inputs.append({'path':s,'reserved_sha256':h,'actual_sha256':a,'match':a==h,'mutable_campaign_ledger':mutable});assert a==h or mutable
contexts={}
for p in [pathlib.Path('openai-proof-research/AGENTS.md'),B/'AGENTS.md',L.parent/'AGENTS.md',B/'ledger.json',L.parent/'ledger.json',B/'prior-campaign-context.json',pathlib.Path('openai-proof-research/sources/upstream.json')]:contexts[str(p.resolve())]=sha(p.read_bytes())
env={'lean_binary':'/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','lean_version':subprocess.check_output(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','--version'],text=True).strip(),'mathlib_rev':json.loads(pathlib.Path('openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json').read_text())['packages'][0]['rev'],'mathlib_dependency_policy':'Read-only existing cache. No upstream rebuild, Lean endpoint, strict replay or axiom audit claimed because no eligible endpoint survived.'}
(L/'verification.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_keys':sorted(res),'chunk_count':20,'chunks':chunks,'reservation_inputs':inputs,'administrative_context_hashes':contexts,'environment':env,'raw_lines_verified':all(sha((L/v['raw_file']).read_bytes())==v['provenance']['raw_sha256'] for v in res.values()),'counts_unchanged':{'accepted_new':2,'target':20,'previous':39},'lane_credit':0},indent=2)+'\n')
print('40 exact keys; 20 manifest chunk hashes verified; no credit; environment recorded')
