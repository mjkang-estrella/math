import pathlib,json,hashlib,datetime,xml.etree.ElementTree as ET
L=pathlib.Path(__file__).resolve().parent
def put(n,t):(L/n).write_text(t.strip()+'\n')
put('SCOUTING.md',r'''
# r246: twelve distinct source-question families

These are twelve attributed questions screened, not twelve currently-open certifications. Related statements within a family are grouped. No old geometric/analytic family is recycled as a fresh survivor. Source bodies were frozen before reading; exact bytes and original/copy bindings are in the *-freeze.json files. All URLs below are versioned primary PDFs. Access occurred in this run, campaign date 2026-10-30. Current arXiv queries are bounded; public-registry heads remain uncleared because previously denied routes stay parked.

R24 = Bandeira–Kireeva–Maillard–Rödder, https://arxiv.org/pdf/2504.20539v1, stable record of 2024 posts, submitted 29 April 2025, document dated June 13 2025.
R25 = Randomstrasse101 authors, https://arxiv.org/pdf/2603.29571v1, stable record of 2025 posts, submitted 31 March 2026, document dated April 1 2026.
P = Petrunin, https://arxiv.org/pdf/2510.11908v2, 7 September 2026 revision.

|# / attributed exact scope|Duplicate status / nearest result actually inspected|Route / decisive next calculation / eligibility objection|
|---|---|---|
|1. Nikolai Nikolov–Mladen Savov, https://arxiv.org/pdf/2307.00545v2, Conjecture 3.7 p5: for every integer k>=3, Q_k=product(j=1..k-1) sum(l=1..j)p_l is maximal among total-degree<=k-1 polynomial lower bounds for the minimum of the full renewal sequence on p_l>=0, sum(l<k)p_l<=1; also largest in the source subclass Ahat_k.|No exact source-ID/author-object history hit in scanned lane SCOUTING/SUMMARY/discovery. Both v1/v2 actual definitions and proofs read. Proposition 3.8 proves only k3; its boundary/determinant argument does not prove k4. Live author/renewal and renewal/maximal/polynomial searches return this same source, not a resolution.|RANK 1: complete maximality refutation at k4, P=Q4+p1*p2*p4. Two full-domain routes in PROOF.md. Strict gain1/64 at uniform p. Independent all-n induction. Strongest objection: extremely short elementary polynomial certificate may be judged routine; current full registries and journal/citing bodies not cleared. No acceptance or priority claim.|
|2. Kireeva, R24 Open Problems7–8 pp6–7: for the multi-frequency SO(2)/finite-group Gaussian synchronization model with uniform signal, find L_n allowing polynomial-time detection at some fixed threshold below1; alternatively fixed L and lambda in(lambda_stat,1), find exp(n^delta), delta<1 detection.|No exact source-ID history collision found; same-family questions grouped. Source explains constant-L low-degree obstruction and exponential exhaustive search. Closest original KBK24 proof not independently retrieved.|Mechanism: exploit cross-frequency identities in growing-L sufficient statistics. Next compute noise variance after frequency convolution. Reject for present investment: complexity lower bounds and two asymptotic limits, no new mechanism.|
|3. Bandeira, R24 Conj9 p8: fixed even r and fixed ell>=r/2, Kikuchi matrix indexed by ell-subsets, M_IJ=lambda+Z_(I symmetric-difference J) when symmetric-difference size r and zero otherwise. After n->infinity, does n^(r/4)*lambda_popout tend to0 as ell->infinity?|Fresh source-ID screen. Actual survey describes known threshold for r/2<=ell<3r/4 and logarithmic-loss general bounds; no original BCSvH24 proof body read.|Moment expansion by overlap diagrams, next isolate ell-dependent leading noise norm. Defer: advanced high-dimensional spectral asymptotics, not a short complete target. Literal source writes lambda_popout as a real threshold while retaining n-scaling; do not silently replace limits.|
|4. Rödder, R24 Open Problem15 p12: SK model with arbitrary external field, does single-site Glauber dynamics mix in polynomial time throughout beta<1?|Fresh source-ID screen. Survey gives beta<0.295 and distinguishes Wasserstein sampling algorithms from total-variation Glauber mixing. Those original proof bodies unread.|Localization/covariance estimate uniform in the external field. Next control susceptibility with both spectral edges. Reject investment: major statistical-mechanics threshold with no elementary route.|
|5. Maillard, R24 Conj6 pp4–5: independent x_i~N(0,I_d/d), does existence of S>=0 with x_i^T S x_i=1 have probability->1 if limsup n/d²<1/4 and ->0 if liminf n/d²>1/4 (equivalently source epsilon-margin clauses)?|Fresh source-ID screen. Actual Theorems3.1–3.2 distinguish small constant exact fitting from bounded-spectrum approximate fitting. No original proof of the sharp approximate theorem read.|PSD cone duality/universality. Next quantify correction of approximate solution without losing PSD. Reject investment: correcting residuals is the hard missing universal bridge, no new mechanism.|
|6. Kevin Lucca, R25 Conj16 pp2–3: for fixed tensor order r, p>=2, arbitrary symmetric deterministic T_i in (R^d) tensor r and independent standard Gaussian g_i, is E||sum g_i T_i||_(injective lp)<=Otilde_(r,p)(d^(1/2-1/p)*sqrt(sum||T_i||²))?|Fresh source-ID screen. Survey proves/describes the p>=2r regime and r=p=2 matrix case, explains volumetric obstruction for p<2r; original covering proof unread.|Generic chaining with tensor geometry. Next cover correlated tensor directions without volumetric exponent. Defer: no improvement to the stated obstruction.|
|7. Daniil Dmitriev, R25 Conj18 pp4–6: for random dense circulant graph G on n vertices (independent symmetric edge-offset choices with probability1/2), E theta(G)=(1+o(1))*sqrt(n).|Fresh source-ID screen. Actual Table1 gives four LP forms; text states lower bound and O(sqrt(n)*loglog n) upper bound. The related Erdos–Renyi conjecture17 is not a separate family/count.|Fourier LP dual construction. Next control largest dual excursions using offset symmetry. Defer; strong random Fourier dependence and original BBD+25 proof not read.|
|8. Vinzant via Bandeira, R25 Conj19 p7: N=4M-5, uniform Grassmannian image of A in C^(N times M), p_M probability x mod unit phase ->|Ax|² injective. Is p_M<1 for every M and p_M->0 as M->infinity? Source naturally requires M>=2 so N>0.|Fresh source-ID screen. Actual body distinguishes known generic4M-4 sufficiency and Vinzant's11 measurements in C4 from this refined probabilistic claim. The old4M-4 necessity is publicly refuted and excluded, not counted as a target.|Rank-two Hermitian kernel intersection and real algebraic geometry. Next estimate probability of a low-rank Hermitian intersection. Defer: full-dimensional Grassmannian probability problem; no novel route. Stability Conj20 is related but not counted separately.|
|9. Luca Ghidelli, https://arxiv.org/pdf/2209.09843v1 pp2–7: if finite-support independent natural-valued X,Y have X+Y uniform on its support, must X,Y each be uniform? Equivalent monic nonnegative real polynomial factors of a0–1 polynomial must themselves be0–1.|No exact ID hit in initial SCOUTING screen. Live query finds later2307.07363 and2608.19173, so no fresh-open clearance. Actual source distinguishes its proved x^5+a*x²+1 case from universal conjecture; infinite power-series counterexamples are not polynomial witnesses.|Positive recurrence coefficients and finite termination. Next inspect newer proof bodies before any attack. Park: overlaps finite/algebraic scout and classical decades-old problem; no significant investment here.|
|10. John M. Campbell, https://arxiv.org/pdf/2304.00360v1 p15, asks symbolic evaluation of sum(n>=0) binom(2n,n)^2/32^n times H_n^(2), H_n², H_(2n)^(2), or H_(2n)². ONE special-function evaluation family.|No exact source-ID history hit. Actual p14 proof resolves a linear harmonic sum using elliptic singular values, not any of these four quadratic/order-two sums. Source's main Sun conjecture is already proved and excluded.|Second derivatives of hypergeometric parameter identities. Next solve the linear system of derivative combinations and identify residual elliptic periods. RANK 2 only as an uncleared search lead: 'symbolically' has no specified target constant class, so writing a generalized hypergeometric derivative would be routine, not a resolution.|
|11. Petrunin / Allcock, P§2 pp2–3: completion B_n of the universal metric covering of C^n minus {z_i=z_j}, with lifted Euclidean length metric: is B_n CAT(0) for every n?|Exact phrase absent from scanned histories. Actual source states n<=3 known, real4-strand case known, and gives convex-function construction forbidding loops. Original Allcock/Charney proofs unread.|Eliminate geodesic digons via convex length functions. Next prove separation of two possible geodesics, not just loops. Reject investment: named high-level ramification conjecture, not an elementary survivor.|
|12. epsilon-delta via Petrunin, P§14 p9: does there exist an embedding closed D4 -> S² times R² whose projection to S² is open?|Exact phrase absent from scanned histories. Actual source constructs abstract open D4->S² via D3 and Hopf projection but says this is not an embedded projection. Original2011 MathOverflow question not retrieved.|Local fiber topology and boundary restriction. Next test whether open projection forces nontrivial2-cycle in the embedded ball. RANK 3 distant only: concrete topology but no full obstruction; original source and closest proof bodies incomplete, no current clearance.|

## Exclusions, not breadth padding

Snake positivity, torus distance energy, two-convex sections, optical fibers, Hilbert quotients, zero-curvature geodesics and Guth sponge were caught in history and not reopened. P postscripts resolved octahedron/cartography/torus norm questions; no solving investment. Seneta's old slowly-varying implication is already proved in Omey–Cadena2211.04565v2 Theorem4(c)->(e), pp4–5 and actual proof chain pp7–15; excluded. R24's signed synchrony and odd Sylvester discrepancy are explicitly retired in its Updates; neither is a new target. Matrix Spencer, Komlos, Hadamard, KLS and Paley headline conjectures were not promoted. No theorem about the other eleven rows is claimed.

Ranking is an investment recommendation, not novelty clearance: renewal maximality is the only completed mathematical survivor. The next useful action is adversarial source/prior-art review of its degree-three polynomial on the whole simplex. Current denied registry routes and older inaccessible intervals must stay parked.
''')
put('PROOF.md',r'''
# A full counterexample to the maximality clause of Nikolov–Savov Conjecture3.7

Primary sources: https://arxiv.org/pdf/2307.00545v1 (2 July2023) pp2–4,6–7 and https://arxiv.org/pdf/2307.00545v2 (1 May2024) pp2–5,6–7. Both actual bodies, including Proposition3.8's closest k=3 proof, were inspected. This is an ordinary-mathematics refutation, held pending independent review and bounded prior-art/eligibility investigation. No novelty or discovery credit is asserted.

## Exact object and endpoint

For k>=3 the source uses probabilities p1,...,pk>=0 summing to1, iid positive integer increments, u0=1 and u_n=sum(j=1..min(n,k))p_j*u_(n-j). It defines m_k=min(n>=1)u_n, Q_k=product(j=1..k-1)(p1+...+pj), and A_k={real polynomials in p1,...,p_(k-1), total degree<=k-1, bounded above by m_k on the whole simplex}. Conjecture3.7 asserts Q_k is maximal in A_k for every k>=3, and a largest-element assertion in a smaller subclass. Maximality means P in A_k and P>=Q_k everywhere imply P=Q_k. A single polynomial dominating Q4 strictly somewhere, but bounded by every renewal mass for every probability vector, disproves this universal statement. It is not enough to improve at one probability vector.

Put x=p1,y=p2,z=p3,w=p4=1-x-y-z, t=x+y+z. Thus x,y,z,w>=0 and t<=1. Define

    Q=x(x+y)t,
    P=x²t+xy=Q+xyw.

P is a real polynomial in x,y,z of total degree3. P>=Q on the entire simplex. At x=y=z=w=1/4, Q=3/32=6/64 whereas P=7/64. Thus P is not Q.

## Route I: direct inequalities and an independent all-time argument

The recurrence gives u1=x, u2=x²+y, u3=x³+2xy+z. The exact differences are

    u1-P=x(1-y-xt),
    u2-P=x²w+y(1-x),
    u3-P=xy(1-x)+z(1-x²).

For the first, xt<=x, so 1-y-xt>=1-y-x>=0. The other two differences are visibly nonnegative since0<=x<=1. Hence0<=P<=u1,u2,u3 and P<=1. The fourth mass is

    u4=w*u0+x*u3+y*u2+z*u1 >= w+(1-w)P >= P.

For n>=5 all four indices n-j are positive and smaller than n, so induction gives u_n>=sum(j=1..4)p_j P=P. This proves P<=u_n for EVERY n>=1 and EVERY point of the simplex, including all boundary points and periodic/degenerate increment laws. In particular it is a valid polynomial minorant even if one defines m by infimum instead of a possibly unachieved minimum. No reliance on the source's printed maximum/minimum typo in(3.1), strictness claims, Blackwell limit, or finite-support reduction is needed.

Consequently P belongs to A4, P>=Q4 throughout the simplex, and P!=Q4. Q4 is not maximal. The universal maximality clause, and therefore literal Conjecture3.7 as a conjunction, is false.

## Route II: barycentric positive-coefficient certificate

Set s=x+y+z+w and work homogeneously at s=1. Homogenize P to degree3 as Ph=x²(x+y+z)+xy*s. Homogenize u1,u2,u3 as x*s², x²*s+y*s², x³+2xy*s+z*s². Their differences from Ph expand to:

    w²x+2wx²+wxy+2wxz+x²z+xyz+xz²;
    w²y+wx²+wxy+2wy²+2wyz+xy²+xyz+y³+2y²z+yz²;
    w²z+wxy+2wxz+2wyz+2wz²+xy²+3xyz+2xz²+y²z+2yz²+z³.

Every coefficient is nonnegative. This separately certifies all initial minorant inequalities on the nonnegative orthant at s=1, without the direct inequalities in Route I. Iterating the positive recurrence then certifies every later mass. Equivalently, the augmented state vector (u_n,u_(n-1),u_(n-2),u_(n-3)) stays in the order interval[P,1]^4 once n=4; its update is a stochastic companion matrix, preserving this interval. The initialization is explicitly certified above.

diagnostics.py checks all symbolic identities over exact rational polynomials, their nonnegative coefficients and1,771 rational simplex points of denominator20. Only the universal symbolic certificates and recurrence induction constitute proof. The grid is a debugging diagnostic.

## Smaller subclass and source fidelity

In cumulative coordinates X=x, Y=x+y, Z=x+y+z, this P becomes

    Phat(X,Y,Z)=XY+X²(Z-1).

Literal v2(2.9) imposes degrees after setting trailing cumulative variables to1: Phat(X,1,1)=X has degree1; Phat(X,Y,1)=XY has degree2; full Phat has degree3. Thus P also refutes the largest-element clause under that displayed v2 definition. However, v1 adds a prose monomial-prefix-degree description after(2.9); read as separate termwise restrictions, it excludes X²Z despite cancellation at Z=1. The v2 removes that prose. Its printed substitution also has an index mismatch. We do NOT rely on this ambiguity for the primary claim. The maximality refutation in A4 is unaffected by every one of these subclass issues and is not a wording/domain correction. No conclusion about largestness under a stronger intended termwise subclass is claimed.

## Scope and credit objections

This answers the literal universal maximality question negatively; it does not classify optimal minorants, prove largestness/nonlargestness in every k, or assert novelty of the polynomial construction. There are no unresolved mathematical quantifiers in the A4 counterexample. Independent review, current full registry coverage, journal-version comparison, citation-network coverage and the substantive-versus-routine credit decision remain unresolved. These are real gates, not an acceptance recommendation disguised as a proof.
''')
put('discovery.md',r'''
# Renewal polynomial investigation

Outcome: a full universal-simplex counterexample to the universal maximality clause of Nikolov–Savov Conjecture3.7, k4. See PROOF.md for both complete routes and all-n verification. The stronger claim about the literal v2 specialization subclass is explicitly separated from the robust main refutation.

The initial route tried P=Q4+xyz. Its three initial-mass gaps are also nonnegative, but it fails the displayed cumulative specialization constraint: after Z=1 a cubic term remains. This was useful but not the final subclass witness. Replacing xyz by xyw produces P=x²(x+y+z)+xy, with a cancellation at Z=1. Both gains agree at uniform probabilities; only the final polynomial is used in the primary certificate. This records the failed subclass route rather than silently discarding it.

The source k3 proof uses boundary saturation and a quadratic determinant. In k4 its conclusion does not extend: Q4 has room in the p4 direction, and the order-three polynomial xy*p4 fits below all renewal masses. The source's generic no-largest-element theorem is not a proof that Q4 is nonmaximal: maximal and largest are different order concepts. Our construction supplies precisely the missing global domination witness.

Precise unresolved scope: all mathematical universal quantifiers needed for the maximality refutation are proved. Largestness under the alternative termwise cumulative subclass is NOT answered. General optimal-minorant classification for k>=4 is NOT answered. No other scout question is solved. New-to-literature status and substantive discovery eligibility remain on HOLD. A short elementary refutation of a literal source conjecture can still be an uncreditable routine observation under campaign standards; root must adjudicate after independent review.

Primary proof-body comparison: v1/v2 definitions and Proposition3.8 proofs inspected in full, as were v1/v2 Proposition3.5/Theorem3.6 arguments. A live search false-positive2607.04467v1 was inspected around its actual Theorem5.3 proof: it concerns special Bernstein-function renewal monotonicity via Gamma averages, not polynomial minorants for arbitrary finite increments. Its recurrence resemblance does not supply the present maximality refutation. No claim of exhaustively reading that whole paper.

Chronology: arXiv API returns original2307.00545 published2023-07-02T11:38:18Z and updated2024-05-01T18:49:07Z. Both versions retain Conjecture3.7. Current author/renewal and renewal/maximal/polynomial searches returned the source without a located later matching resolution. This does not clear non-arXiv, journal, specialist databases or currently inaccessible public proof registries. No denied route was retried. Older inaccessible historical intervals remain parked.
''')
put('SUMMARY.md',r'''
# r246 handback — mathematical counterexample; novelty/credit HOLD

Twelve distinct attributed source-question families screened. The fresh strongest survivor is Nikolov–Savov2307.00545v2 Conjecture3.7, universal polynomial-minorant maximality for renewal masses. At k4, Q4=x(x+y)(x+y+z) is globally dominated by P=x²(x+y+z)+xy=Q4+xy*p4, a degree-three polynomial below EVERY renewal mass for EVERY probability vector. Strict gain1/64 at uniform p. PROOF.md gives direct inequalities/all-n induction and a separate positive-coefficient barycentric certificate. Exact diagnostics pass1,771 simplex points plus symbolic identities.

The robust maximality refutation is independent of source typos and subclass ambiguity. Literal v2 specialization-defined subclass also contains P, while a different v1 prose termwise interpretation may exclude it; no stronger intended-subclass result is asserted. Full source/journal/current registry novelty clearance and independent substantive review are still needed. The elementary-shortness objection is explicit; no discovery credit proposed automatically.

Counts unchanged9 additional/39 total/next40; root alone accepts/counts. All writes in assigned lane. Solo; no children, git, public/browser/MathDB, shared, Lean or manuscript edits. Search-response overwrite failure is documented in FAILURES.md. Final manifest excludes itself and verification receipt, with separate guarded verification after writes.
''')
put('progress.md',r'''
Completed: rules/admin snapshots, recent-scout comparison, early exact-ID/alias history screen, twelve-family breadth report, both primary target versions frozen/read, source closest proof comparison, two full-scope mathematical routes, exact bounded diagnostics, primary-access/chronology ledger, final manifest.

Remaining acceptance gates: independent adversarial source/prior-art review, journal body/version check, available lawful current registry comparison, novelty and substantive credit ruling. These are not performed by this scout. Do not retry denied access routes. No claim on other questions or the stronger intended cumulative subclass. No request to update counts.
''')
put('FAILURES.md',r'''
1. Initial native file inventory was too broad and its output truncated. It performed no write; subsequent reads/searches were bounded and helpers/retrieval/hashing ran under the required guard.
2. Second search run reused sources/search0.xml, search1.xml and their corresponding frozen paths, overwriting the initial title-search responses before preservation. Those initial responses are NOT claimed as retained immutable evidence. Their tool output persists in the session, but no recoverable original-byte hash is asserted. Target PDFs/text, chronology evidence and current/prior search files were not overwritten. Current files named search0/search1 contain the later date-bounded2018–2023 queries. Later searches use distinct current*/prior* names. This failure does not affect any mathematical source binding or certificate.
3. Initial xyz improvement fails the smaller specialization-defined subclass; final xyw improvement supersedes it. Neither an invalid theorem nor a failed resource run is concealed.
4. pdftotext emitted a font mismatch warning for an exploratory PDF; downloaded originals are retained and text copies separately hashed. Target renewal PDFs extracted cleanly. Source equations carry printed typos; the proof independently derives the recurrence quantities.
5. No HTTP403/429/challenge or cap termination occurred in this lane. Previously denied GitHub/ScienceDirect/challenge routes were never requested. Current registry head coverage remains explicitly unavailable, not treated as clearance.
6. Initial comparison reads of recent scout summaries preceded their explicit immutable-reference hashing. They were subsequently hash-bound and reread under the guard in reconcile mode. This corrects the retained comparison evidence but does not retroactively satisfy freeze-before-first-read for those summaries. All external scientific target PDFs and derived text were frozen before first scientific reading; the final target proof does not depend on the earlier summaries.
''')
put('RUN.md',r'''
# Reproduction

From this lane, run each command through the required absolute helper:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python diagnostics.py

diagnostics.py uses SymPy for exact algebra, no random seed or floating tolerance. Resource envelope remains AS512MiB / sampled process-group RSS512MiB / CPU210s / wall230s with one BLAS/OMP thread, no cap raises. Observed diagnostics peak sampled RSS54,460,416bytes and wall0.882s. The final verification is a distinct guarded process:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python verify.py

Do not rerun exploratory search commands into existing paths: see FAILURES.md. Manifest recreation is deliver.py; verification occurs afterward in a separate process. Administrative originals may change due to root/concurrent work and are snapshot-only; verifier checks their copies only. Scientific originals and copies are both rechecked.
''')
records=[]
for p in sorted((L/'sources').glob('*')):
 if p.is_file():records.append({'path':str(p.relative_to(L)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
chron=[]
for p in (L/'sources').glob('*.xml'):
 try:
  root=ET.fromstring(p.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
  for e in root.findall('a:entry',ns):
   if '2307.00545' in e.findtext('a:id',default='',namespaces=ns):chron.append({k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']})
 except ET.ParseError:pass
pro={'lane':L.name,'generated_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'full ordinary-math maximality refutation; novelty and credit HOLD','counts':{'additional':9,'total':39,'next':40,'authority':'root only'},'scientific_sources':records,'target_chronology':chron,'source_urls':['https://arxiv.org/pdf/'+p.stem for p in (L/'sources').glob('*.pdf')],'closest_proof_bodies':['2307.00545v1 Definitions2.5–2.9, Conjecture3.7, proof Proposition3.8','2307.00545v2 same; pp2–7','2607.04467v1 Theorem5.3 proof context'],'current_clearance':'bounded arXiv queries only; denied public registries parked','resource_caps':{'AS_MiB':512,'groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230},'access_policy':'no denied-route retries; stop403/429/challenges; no browser/proxy/TLS bypass','known_failure':'initial exploratory title-search responses overwritten; not retained as evidence'}
(L/'provenance.json').write_text(json.dumps(pro,indent=2))
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2))
print('Wrote reports and manifest:',len(manifest),'files')
