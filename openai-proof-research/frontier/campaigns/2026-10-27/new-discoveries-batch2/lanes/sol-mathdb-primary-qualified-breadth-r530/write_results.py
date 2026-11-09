import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parent;L=D.parent;B=L.parent
notes={
368994:'Unbounded chi/r requires a family for every c; a fixed high-chromatic graph or existing sublinear separation does not supply that family. No full-scope construction found.',
369005:'Literal text itself reports a 1996 theorem for exactly nontrivial nilpotent H in finite nonabelian simple G. HOLD_REPORTED_PRIOR: original theorem body not checked; do not reinvest as a new conjecture.',
369037:'Improving 4m to 3m needs a universal irregularising-walk mechanism. Subdivided-star examples only test sharpness, not the upper bound. No full route; no repeat of edge-irregulator helper work.',
369038:'Literal text reports counterexamples at r=3,4 and names a counterexample source. HOLD_REPORTED_PRIOR; no original refutation body checked here, no discovery claim.',
369051:'Literal arbitrary d includes d=0, where a random 2-factor need not be Hamiltonian; this is a domain/wording issue, not an eligible refutation of the intended source conjecture. Source quantifiers unread; HOLD.',
369116:'Cleaning is a game invariant, not simply visiting vertices along a walk. A uniform strategy for all connected G is required; small-graph evidence and Heawood obstruction do not establish the guarantee.',
369134:'Needs a superlinear size-Ramsey lower bound already for fixed d=3 and unbounded n. A finite example gives no epsilon-family. No full-scope mechanism.',
369159:'Universal spanning embedding at exact degree threshold includes arbitrary bounded-degree H. Greedy packing loses the threshold; announced proof in literal text is not body clearance. HOLD.',
369256:'Literal text says source main theorem settles this threshold, conflicting with open metadata. HOLD_REPORTED_PRIOR; no independent primary theorem audit; no new target.',
369257:'Linear exponent for every s>3 is stronger than the reported t^(2/3) bound. Finite Ramsey instances cannot certify the asymptotic family. No mechanism.',
369288:'Supremum over all admissible degree sequences must be uniform in n. A random-regular calculation alone misses nonregular sequences and does not prove the limsup statement.',
369384:'Primary Conjecture25 matches all positive irrational alpha. Definition(2) uses floors alpha^2 n minus alpha floor(alpha n). Existing Proposition23/24 arguments use Kronecker; the source explicitly warns the converse for p>=2 is limited. No uniform treatment of rational dependence among 1,alpha,alpha^2; PARK without another sweep.',
369435:'All C2 bounded planar domains and all a>0 demand a sharp spectral comparison and rigidity. Disk perturbations or a single parameter do not settle full Faber-Krahn. No short mechanism.',
369522:'For each g>=2 one needs convergence in probability of an optimization parameter as even d grows. Free-probability heuristics do not prove the matching extremal upper bound; definitions/body unreviewed.',
369564:'Connectivity alone plus a linear out-degree threshold must route every prescribed pairing for all k. Polynomial linkage bounds do not give the claimed absolute C; no replacement mechanism.',
369584:'Exact 3n/4 decomposition for all fixed girth targets requires both divisibility and global absorption. Approximate triangle packings leave an uncovered-edge gap. No low-burden full route.',
369592:'EXCLUDE_SOURCE_SUPPLIED_COUNTEREXAMPLE: Section5 Conjecture4 is the exact target. Corollary3 proof supplies explicit integer 2x16 real/imaginary X, A=X*X, and reported ratio 1.029822>1. Read actual construction and proof passage. Exact arithmetic certification of that already supplied witness would be a helper/formalization, not discovery. Numerical spectral inequality not independently replayed.',
369644:'Need additive overhead independent of clique size and graph order for all bounded-mad backbones in chordal G. Degeneracy gives multiplicative palette losses; no additive full construction.',
369666:'Exact binomial value for every k,t requires both extremal construction and upper bound. Reported Theta growth and t=4,5 cases are insufficient; boundary tests would be parameter instances only.',
369726:'Conjunction requires maximum time bound and every intermediate time for all d, not merely pt=1. A coordinate half-cube supplies only the easy endpoint, excluded as helper.',
369988:'IU size bound is not a sturdiness bound; beta definition must be read in primary body before attempting local counts. No claimed proof from |G|<=2^(n-2). HOLD.',
370067:'All m requires classifying maximum m-distance configurations or constructing one in the deletion family. Small hexagons for m=4,6 cannot provide a universal mechanism.',
370094:'Source defines re as edge-disjoint decomposition, not cover. Section6 Conjecture6.3 actually asks re(G)<=n-1, stronger than this literal O(n) cover formulation. Cannot turn a cover/decomposition or wording correction into credit. No all-graph linear decomposition route.',
370095:'Primary Conjecture6.4 is odd-regular edge-disjoint decomposition <=n-1; source explicitly makes perfect-matching case easy via Petersen. Missing odd-regular graphs without perfect matching remains. No certificate or reduction closing that gap.',
370102:'Full 2<=d<=n/2 expected online discrepancy bound needs an algorithm robust over the dense regime and lower bounds. Sparse-range result does not extend by replacing d in an estimate.',
370153:'For every fixed k, asymptotically sharp triangle counting in suspended-path-free graphs is global extremal work. Local neighborhood path bounds alone lose the proposed leading constant.',
370247:'General Ore-degree7 strong edge-coloring needs all such graphs, beyond the planar result. Finite bounded-degree searches cannot certify all graph orders; no discharging substitute without planarity.',
370257:'Claim includes 13-vertex uniqueness as well as minimum order. Exhausting signed graphs below13 and all extremals would be large; figure and negative-girth conventions unread. HOLD, no broad enumeration.',
370278:'Need uniform linear-in-ell exponent for every fixed r>=4. A few cycle density calculations or known r=3 inequality does not supply the higher-order analytic mechanism.',
370303:'Universal six-color injective edge coloring for subcubic graphs needs structural reductions for arbitrarily large order. Greedy conflicts can exceed six; small examples would not settle it.',
370320:'Two infinite coefficient sign patterns require all coefficients of product and reciprocal. Bounded q-expansion is only evidence; no sign-preserving dissection identity found or claimed.',
370330:'Primary Definition2.1/2.2 and Conjecture6.1 match all tournaments over F2. Lemma6.2 proof gives full-rank principal blocks, but Section6 explicitly leaves preservation of the decycling property under B+C^T A^-1 C unresolved. Ordinary Schur rank additivity is not the missing combinatorial bridge. PARK; no independent full route.',
370347:'All finite Coxeter types and all concordant u need both semidistributivity and regular Hasse degree r-1. Rank-specific enumeration misses exceptional and unbounded types; definitions body unread.',
370354:'Asymptotic delta->1/2 must hold with unbounded width as incomparability degree grows. Fixed-width results do not provide uniform constants; no full distributional argument.',
370355:'Unbounded gap must force unbounded entropy parameter across all finite posets. A few expectation gaps do not control entropy of restrictions; primary varsigma definition needed. HOLD.',
370374:'Kernel W_alpha and parameter domain absent from literal definition. Exact energy comparison cannot start from unspecified kernel or numerical configurations. HOLD_SOURCE_DEFINITIONS.',
370435:'Upper bound f(n)<=3 requires excluding all higher-degree flawless factorizations for every even n; cubic examples prove only known lower bound. No universal obstruction developed.',
370521:'All ambient G and all matching precolorings require extension at Delta+3; includes difficult total coloring when matching empty. Planar high-degree theorem does not transfer to arbitrary graphs.',
370526:'Literal text reports its theorem constructs counterexamples in the exact type-I family. HOLD_REPORTED_PRIOR; original construction body unread. No recertification credited.',
370580:'All degrees and real p>=2 require sharp interpolation across non-even exponents. The power trick gives a ceiling and ordinary norm interpolation does not remove it. Known d<=4 or p>=6.8 are excluded instances; no full route.',
370731:'Perfect 1-factorization for every even n is a global construction problem. Prime-order constructions and any single n (including64) are parameter instances, no full uniform mechanism.',
370817:'For every forest T need polynomial chi bound for all T-free G; proving a few forests or an exponential chi-bound misses polynomial dependence. No full-scope route.',
370827:'Literal equal opposite directed-connectivity definition already fails for one-edge K2 under either orientation; intended well-balanced notions require primary definitions. Wording correction earns no credit; associated resolved claim in record not independently body verified. HOLD.',
370890:'Primary Conjecture2 matches all k<=d-1. Theorem2.6 proof read establishes hyperplane case by odd/even coordinate counting; it does not control higher-codimension affine sections. No extremal centralization mechanism.',
370891:'Primary Conjecture3 is every centrally symmetric polytope, with source implication to cube sections. Maximizing edges crossed by a hyperplane does not trivially move it through center; no finite exact obstruction developed. No claim from cube theorem to all polytopes.',
370928:'For every odd-cycle orientation needs a function d_F(k) working for every k and ambient digraph. Established C3,C5 cases are not full scope; no extension mechanism.',
370942:'Primary Definition1.1 and Conjecture3.2 confirm all positive a,b,c with a,c>=2, no coprimality restriction in target. Exact bounded search a,c<=100, exponents<=24,b<=10^6 found no triple. This cannot prove the universal bound or fixed-equation completeness. Source algorithm also uses a custom axiom, not an allowed formal certificate. PARK.',
370957:'Literal text explicitly reports Calegari-Dimitrov-Tang proof of the full conjecture. HOLD_REPORTED_PRIOR; original theorem bodies unread. Prime-specific refinement is a different question and not substituted.',
371010:'Need codegree-relative (1+epsilon2) bound uniformly for all sufficiently large Delta under fixed epsilon1,epsilon2. Claw-free bound does not cover general graphs; no full route.',
371028:'Density-one statement requires exact ordering/measure and genus quantifiers from primary source. A low-degree point on individual curves is not an asymptotic density theorem. HOLD_SOURCE_QUANTIFIERS.'}
rows=json.loads((D/'assigned-records.json').read_text());out=[]
selected={369384:'2507.14244',369592:'2508.00111',370330:'2509.10232',370942:'2510.11753',370890:'2510.09265',370891:'2510.09265',370094:'2509.01901',370095:'2509.01901'}
for x in rows:
 r=x['record'];i=r['mathdb_id'];s=r['statement'];out.append({'mathdb_id':i,'corpus_path':x['corpus_path'],'corpus_line':x['line'],'statement_utf8':s,'statement_utf8_sha256':hashlib.sha256(s.encode('utf-8')).hexdigest(),'canonical_record_sha256':x['record_sha256'],'canonicalization':'json.dumps(record,ensure_ascii=False,sort_keys=True,separators=(comma,colon)), UTF-8','source_url':r['source_url'],'disposition':'EXCLUDE_SOURCE_SUPPLIED_COUNTEREXAMPLE' if i==369592 else 'HOLD_NO_QUALIFIED_FULL_SCOPE_ROUTE','technical_read':True,'reason':notes[i],'primary_passage_review':selected.get(i),'whole_body_review':False,'full_dependency_review':False,'successor_body_clearance':False,'current_registry':'HOLD_UNAVAILABLE','credit':0})
assert len(out)==50 and len(notes)==50
(D/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(D/'proposals.json').write_text('[]\n')
# Bind guard and needed contextual files, without copying trees.
refs=json.loads((D/'flat-bindings.json').read_text())
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',B/'AGENTS.md',B.parents[3]/'AGENTS.md']:
 if p.exists():
  b=p.read_bytes();refs[str(p.resolve())]={'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(D/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
context=[]
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/name;v=json.loads(p.read_text());context.append({'path':str(p),'content':v})
(D/'context-review.json').write_text(json.dumps({'r304_reconciliation':'Accepted families and historical objections read structurally after binding; no proposal promoted. Cayley r363 decision read; r529 current adjudications control.','accepted_scope_titles':[f.get('title') for f in context[0]['content']['families']],'historical_top_level_keys':list(context[1]['content']),'counts':{'additional':9,'total':39,'next':40}},indent=2)+'\n')
print('wrote',len(out),'dispositions; proposals 0; accepted titles',len(context[0]['content']['families']))
