import pathlib,json,hashlib,re,datetime,resource,subprocess
resource.setrlimit(resource.RLIMIT_AS,(1500*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(60,60))
L=pathlib.Path(__file__).resolve().parent.parent;B=L.parent.parent;P=pathlib.Path('/home/mj-kang/Documents/Dev/math');D=json.loads((L/'extracted.json').read_text());H=json.loads((L/'history-id-title-matches.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
# Classify search matches conservatively: numerical substrings/OEIS names are not target history.
for i,matches in H.items():
 for x in matches:
  s=pathlib.Path(x['path']).read_text(errors='replace');title=D[i]['record']['title']
  x['classification']='administrative_current_reservation' if x['path'].endswith('new-twenty-2026-10-31/ledger.json') else ('possible_exact_history' if re.search(r'(?<![A-Za-z0-9])'+i+r'(?![A-Za-z0-9])',s) or title.lower() in s.lower() else 'unrelated_numeric_hash_or_OEIS_substring')
(L/'history-classified.json').write_text(json.dumps(H,indent=2)+'\n')
notes={
'343531':'Needs full asymptotic extremal improvement for K4,6; finite norm-graph examples do not establish little-oh.',
'343542':'Needs injective coprime labeling attaining 7k or7k+1 for all k, and sharp lower bound; source body unread.',
'343543':'Needs source definition of stacked levels and all-k,n coprime construction; possible n=1 wording issue not eligible as discovery.',
'343554':'Literal repeats conjecture as premise. Recover minimum-safe-set definition and source quantifiers; no tautological proof eligible.',
'343595':'Needs exact thermograph/temperature definition and all-board bound or finite game counterexample with certified semantic recursion.',
'343653':'Needs full equitable Delta-coloring outside all listed exceptions; no general coloring construction obtained.',
'343654':'Needs measurable invariant-probability coloring for unrestricted average degree; finite graph evidence does not bridge Borel scope.',
'343697':'Needs primary exact annulus optimizer and arbitrary two-boundary planar-domain comparison; no shape-variation certificate.',
'343875':'Needs universal k-color component threshold, not fixed-k small examples; no extremal construction meeting degree obtained.',
'343877':'Needs geodesic minimizing-index definition and lower bound excluding all k<2p for all odd primes.',
'343878':'Paraphrase omits graph-embedding restriction and ambiguous signed-genus notation; recover source before reasoning, no unbounded-graph correction credited.',
'343900':'Needs universal mad-partition lemma for real c1,c2; testing finite partitions would not prove the all-graph claim.',
'343921':'Full illumination bound/equality classification in all d>=3; no tractable new mechanism selected.',
'343931':'Needs precise metric/graded structure, largest-Carnot-subgroup definition and both Markov-convexity transfers.',
'343951':'Needs rainbow transversal for all degree-two graphs and n; independent-set versus matching equivalence needs source bridge.',
'343953':'q undefined in record; source parameter definition mandatory before exact endpoint selection.',
'344011':'Needs construction realizing every nonzero integer as an extreme cyclotomic coefficient, not merely height or an interior coefficient.',
'344110':'Independent domination inequality is universal in both graph factors; stronger known false product inequality is not this target.',
'344116':'Averaging-operator norm must be restricted off constants in the source. Full arbitrary-modulus super-approximation remains uninvestigated; no domain-fix credit.',
'344131':'Needs greedy process never stopping, including rightmost insertion/earliest-letter priorities; arbitrarily long finite runs are insufficient.',
'344204':'Needs all n and r<=n intersecting independent-set bound with exact largest-star formula.',
'344318':'Needs asymptotic maximal prime-gap bound; finite exact prime computation cannot supply it.',
'344382':'Needs full two-subgraph edge partition and weight-coloring certificates for arbitrary graph; no general mechanism.',
'344388':'Needs primary persistence/possibility quantifiers in switching Moran model; finite model paraphrase is insufficient for any extinction objection.',
'344454':'Needs source asymptotic additive-constant convention and universal 3n/7 matching lower bound; small-n endpoint artifacts excluded.',
'344466':'Needs full infinitesimal stabilizer valuation ring proof or actual dp-finite countermodel; no finite algebra surrogate.',
'344560':'Needs source quantifiers for fixed t versus total-clique objective and exact remainder convention. Possible t=2 tie degeneracy is not significant.',
'344574':'Needs probability upper tail O(alpha^4) in infinite median dynamics; stable-square lower bound alone is not the assertion.',
'344582':'Needs comparison over entire genus-two moduli space, not a few curves on Bolza.',
'344612':'Needs Lipschitz-free polytope volume-product inequality in arbitrary dimension; low-dimensional certificates do not resolve it.',
'344659':'Needs precise corner-angle and point-spectrum convention, and finite total eigenvalue count; smooth-domain special cases cannot refute exact corner scope.',
'344728':'Needs all planar graphs feedback-vertex/cycle-packing inequality, not already known subcubic case.'}
selected={
'343459':('hold_material_prior_source_gap','primary_definitions_and_minimum_distance_proofs; published_conjecture; independent_full_finite_diagnostic','1908.03513','10-vertex full-scope diagnostic counterexample; prior2023 thesis abstract explicitly reports same conjecture counterexamples. ChapterV proof body unread; route stopped. See ATTEMPTS.md.'),
'343487':('hold_no_full_four_point_inequality','primary_definitions_and_bound_proof','1908.04440','Source Conjecture6.5; Hilbert embedding only gives sqrt2 bound. Need powered Euclidean four-point upper bound and scalability bridge; no endpoint.'),
'343537':('excluded_public_exact_refutation','primary_definitions_and_conjecture; later_Theorem1.1_Proposition3.1_proof; independent_all_subset_reproduction','1908.05879','Allikvere2607.28813 public July2026 refutation; explicit11-vertex G1 only resolved by whole vertex set, independently reproduced. No global minimality audit.'),
'343558':('excluded_source_already_refutes','primary_definitions_gadgets_Lemmas5_6_Theorem7_proofs','1908.06697','Source Theorem7 and Corollary8 refute stronger Barát conjecture as well as Thomassen; exact full-scope source bridge read.'),
'344115':('hold_uniform_separator_lemma','primary_two_language_definitions_and_conjecture; bounded_flow_diagnostic_and_structural_attempt','1910.05675','108 exact diagnostic cases agree through n7; O downset and I endpoint-deletion connectedness do not prove kappa=delta. Need uniform surviving cross-fiber boundary lemma.'),
'344325':('hold_FEM_and_spectral_bridges','primary_coarsening_projector_definitions_degree2_calculation_conjecture; conditional_Schur_complement_derivation','1910.13792','Conditional exact z^2/2 curvature recurrence derived beyond commuting/eigenvector shortcut. Need all-degree FEM kernel/base-curvature and rigorous eigenbranch/Lean bridges; later2403.02139 only text-screened.'),
'344511':('excluded_source_exact_theorem','primary_Conjecture1.2_Theorem1.3_final_proof_read_supporting_lemmas_not_fully_audited','1911.06435','Exact primitive-weight theorem already in source Theorem1.3; compactness/final proof read; not new.'),
'344734':('excluded_source_exact_theorem','primary_Theorem1_Lemmas1_2_3_and_final_induction_proofs','1912.01600','Chase published2020 Theorem1 already gives literal triangle bound. Complete five-page mechanism read.')}
results={}
for i,x in D.items():
 d=x['record'];out,depth,src,reason=selected.get(i,('hold_statement_only_no_qualification','literal_record_only',None,notes.get(i,'')))
 results[i]={'mathdb_id':int(i),'title':d['title'],'outcome':out,'accepted_credit':0,'inherited_matches':H[i],'inherited_target_exclusion_found':False,'new_review_depth':depth,'primary_definitions_recovered':i in selected,'literal':{'raw_file':f'raw/{i}.jsonl','statement':d['statement'],'statement_sha256':x['statement_sha256'],'raw_sha256':x['raw_sha256'],'chunk':x['chunk'],'chunk_sha256':x['chunk_sha256'],'line_one_based':x['line_one_based'],'newline_preserved':(L/f'raw/{i}.jsonl').read_bytes().endswith(b'\n')},'source':{'url':d['source_url'],'name':d['source_name'],'primary_download':f'sources/{src}.pdf' if src else None,'pdf_sha256':sha((L/f'sources/{src}.pdf').read_bytes()) if src else None,'receipt_files':['sources/initial-receipts.json','sources/receipts.json','sources/final-receipts.json'] if src else [],'publisher_body_status':'read exact conjecture in codes-published.pdf' if i=='343459' else 'not separately checked unless downloaded arXiv document itself is journal-formatted'},'mathematical_attempt_or_remaining_lemma':reason,'details':'ATTEMPTS.md' if i in selected else None,'lean_endpoint':None,'novelty_clearance':False,'limit':'Metadata open/full labels do not establish unresolvedness or source completeness. No current MathDB/Palomar clearance.'}
assert len(results)==40
(L/'results.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
# Reconstitute original dated successful receipts from observed tool responses, with file hashes recomputed.
names=['registry-head','1908.03513','1908.05879','1910.13792','1908.06697','1911.06435','1912.01600'];times=['10:26:18.510058','10:26:20.013513','10:26:20.160434','10:26:20.491687','10:26:20.668726','10:26:20.796099','10:26:20.965190'];r=[]
for n,t in zip(names,times):
 p=L/f'sources/{n}.';p=L/'sources'/(n+('.json' if n=='registry-head' else '.pdf'));r.append({'name':n,'url':'https://api.github.com/repos/OpenAI/math/commits/main' if n=='registry-head' else f'https://arxiv.org/pdf/{n}','utc':f'2026-11-01T{t}+00:00','status':200,'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size,'receipt_provenance':'original fetch tool stdout; hash independently recomputed'})
(L/'sources/initial-receipts.json').write_text(json.dumps(r,indent=2)+'\n')
# Verify complete twenty-chunk binding against inventory manifest.
C=B/'lanes/pi-mathdb-full-corpus-inventory-r301';M=json.loads((C/'manifest.json').read_text());cv=[]
for f in M['files']:
 if f['path'].startswith('corpus/mathdb-normalized-chunk-'):
  h=sha((C/f['path']).read_bytes());assert h==f['sha256'];cv.append({'path':str(C/f['path']),'sha256':h,'matches_manifest':True})
assert len(cv)==20
(L/'corpus-manifest-verification.json').write_text(json.dumps({'manifest':str(C/'manifest.json'),'sha256':sha((C/'manifest.json').read_bytes()),'chunks':cv},indent=2)+'\n')
T=B/'new-twenty-2026-10-31/fresh-corpus-r5/openai-preprints.body';tree=json.loads(T.read_text());assert tree['sha']=='3f56f68a176b4494c346091ea0a319651bc217ec' and not tree['truncated'];terms=['mallik','yildiz','multiset','toeplitz','fibonacci','quasi-hyperbol','von-neumann','coprime','rainbow','snort']
hits=[x['path'] for x in tree['tree'] if any(t in x['path'].lower() for t in terms)]
(L/'sources/registry-reuse.json').write_text(json.dumps({'head':json.loads((L/'sources/registry-head.json').read_text())['sha'],'head_checked_utc':r[0]['utc'],'complete_preprints_tree':{'path':str(T),'sha256':sha(T.read_bytes()),'git_tree_sha':tree['sha'],'entries':len(tree['tree']),'truncated':False},'path_search_terms':terms,'path_hits':hits,'limits':'Path screening only; no all-body absence/novelty clearance. Root tree cache truncated. MathDB/Palomar inherited403, not retried and not clearance.'},indent=2)+'\n')
lean=P/'dlp-research/.tools/lean-4.34.1-linux/bin/lean';mp=P/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages';manifest=P/'openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json'
env={'lean_binary':str(lean),'version':'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)','version_provenance':'Earlier successful direct --version tool output; subsequent calls under RLIMIT_AS failed creating runtime threads; failure logs retained','binary_sha256':sha(lean.read_bytes()),'packages_read_only_path':str(mp),'mathlib_expected_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','lake_manifest':str(manifest),'lake_manifest_sha256':sha(manifest.read_bytes()) if manifest.exists() else None,'formal_work':'None: no endpoint survived qualification; no axioms audit or strict replay claimed.','cache_trust':'No full upstream rebuild/source-to-olean attestation; no dependency edits.'}
if manifest.exists():env['mathlib_manifest_entries']=[x for x in json.loads(manifest.read_text()).get('packages',[]) if x.get('name')=='mathlib']
(L/'environment.json').write_text(json.dumps(env,indent=2)+'\n')
print('40 results;20 manifest chunks;8 primary target reviews;32 literal-only;0 credit')
print('unexpected history matches',[(i,x['path']) for i,a in H.items() for x in a if x['classification']=='possible_exact_history'])
