import pathlib,json,hashlib,datetime,re
L=pathlib.Path(__file__).parent
def h(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
def w(n,t): (L/n).write_text(t if isinstance(t,str) else json.dumps(t,indent=2))
bindings=json.loads((L/'scientificbindings.json').read_text())
for b in bindings:assert h(pathlib.Path(b['original']))==h(pathlib.Path(b['copy']))==b['sha256']
for p in (L/'sources').iterdir():
 if p.suffix=='.txt':continue
 q=L/'frozen/live'/p.name
 if not q.exists():
  # Indexes retrieved before copy-on-fetch was added; their receipt hash already
  # preceded reading. Preserve that sequencing limitation explicitly below.
  q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
 assert h(p)==h(q)
 bindings.append({'original':str(p),'copy':str(q),'sha256':h(p),'kind':'retrieved primary/metadata'})
w('scientificbindings.json',bindings)
assert h(L/'frozen/r237/sources/wong7.pdf')==h(L/'sources/wong-current.pdf')
w('source-postread-checks.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'all_original_copy_bindings_pass':True,'wong_cached_equals_live':True,'bindings':len(bindings)})
w('discovery.md',r'''# Source target and exact reduction; unresolved ordinary proof

Let m be a positive integer and let a1,a2,a3,a4,K be integers in [0,m-1]. Entries are indexed and may coincide. Put
S = sum_{j=0}^K sum_{T subset {1,2,3,4}} (-1)^(4-|T|) floor((j+sum_{i in T}ai)/m).
The target is S >= -3 floor(m/3), for ALL these parameters, with no parity or divisibility restriction.

Literal source: Thanatipanonda–Wong, JIS21 (2018), Article18.1.8, Section4 pp14–15; the independent sentence 'We conjecture the lower bound' on p15 gives this inequality. Table1 p2 also lists it. It is consequently not an invented fragment of Conjecture17. The latter, pp16–17, has additional all-n extremizer and recurrence assertions; its n4 example assumes m multiple3. No full-C17 resolution is asserted here. The source writes sets, but its repeated-entry extremizers and the 2017 predecessor's explicit multiset Definition1 settle the intended indexed convention. The subset sign is positive for sizes0,2,4 and negative for sizes1,3; the empty subset is included.

Chronology: Onphaeng–Pongsriiam received Sept28 2016, published Jan14 2017; Thanatipanonda–Wong arXiv v1 Aug10 2017, v2 Feb14 2018, JIS published Feb23 2018. The live JIS PDF retrieved Oct30 2026 has the same SHA256 as the r237 original. All hashes are in scientificbindings.json and retrieval.jsonl.

Nearest proof actually read: Onphaeng–Pongsriiam, Article17.3.6, Definition1 p2 and Theorem9 proof pp15–19. It expresses the alternating subset sum through signed two-variable Jacobsthal blocks and applies 0<=S2<=floor(m/2). Its general conclusion is -2^(ell-2)floor(m/2)<=S_ell<=2^(ell-2)floor(m/2); sharp lower/upper witnesses use respectively odd/even ell AND even m, all entries m/2, K=m/2-1. It does not establish the requested even-ell lower bound. Wong Theorem15 p15 combines two- and three-variable bounds to give only -2floor(m/2)-floor(m/3). Wong Theorem16 records the predecessor's parity sharpness with m even, not a new proof of our target.

## Exact quotient/remainder route
Write H=K+1, so 1<=H<=m. For each subset let s=sum ai=qm+r with 0<=r<m. Directly splitting j=0,...,H-1 at j=m-r proves
F(s)=sum_j floor((j+s)/m)=Hq+max(0,r+H-m).
Thus S is the signed sum of these sixteen F(s). This includes equality at r+H=m and H=m. It loses no residue term.

There is also a quotient-free formula. Since 0<=j+s<5m, count the thresholds lm, l=1,...,4. With C_H(u)=max(0,min(H,u)), exactly C_H(s+H-lm) of the integers j in [0,H-1] satisfy j+s>=lm. Therefore
F(s)=sum_{l=1}^4 C_H(s+H-lm).
The equality is integral, including s=0, H=1,m and all threshold boundaries. Each floor is nonnegative here, so threshold counting has no negative-level correction. Both formulas were compared exactly against the defining sum for every sorted tuple and every K through m=24.

This gives a finite piecewise linear INTEGER formulation, not a continuous approximation. Introduce integer t>=0 with 3t<=m<=3t+2; then t=floor(m/3). The counterexample condition is the finite sum of 64 clipped linear terms < -3t. Sorted a1<=a2<=a3<=a4 is valid: permuting the four labels bijects all subsets and preserves their signs and sums. No complement or rotation reduction is used in the solver.

all-m-query.smt2 encodes precisely these constraints. Z3 5.3.3 returns UNSAT, both in the default run and a separate proof-producing run. z3-proof.sexpr is an emitted solver proof object. It has NOT been independently checked and has NOT been converted to an ordinary proof. This computational conclusion is a strong lead, not a certified resolution, novelty claim, or eligible credit. A small independent exact checker or an ordinary chamber/Farkas argument remains necessary. Do not infer acceptance from the .sexpr extension or the UNSAT result.

## Cyclic cancellation route
For n>=2, changing any entry ai by m changes each affected floor by1; the signed sum of those constants is (1-1)^(n-1)=0. Also sum_{j=0}^{m-1}floor((j+s)/m)=s for nonnegative integer s, since s=qm+r gives mq+r=s. Alternating the linear s over subsets proves a full period sums to0 for n>=2.

Let bar ai=(-ai mod m). Before canonical reduction take m-ai, which may equal m. The integer identity floor((-x-1)/m)=-floor(x/m)-1 gives f_{m-a}(m-1-j)=-f_a(j); the |T| and constant corrections cancel in the subset sum. Consequently S_bar_a(m-2-K)=S_a(K) for 0<=K<=m-2. K=m-1 separately gives0. Thus any complement reduction must transform K too. Arbitrary starting-index rotations do not preserve a prefix sum, so none is asserted.

Finally f4(j)=f3(j+a4)-f3(j), by splitting subsets according to membership of4. Hence S4 is the difference of two cyclic interval sums of f3 of length H. This proves cancellation but the existing separate interval bounds do not yield the requested residue-sensitive estimate. No sign-run classification has been proved. The solver formulation is the stronger next route, provided its certificate can be checked independently.

## Prior scope
Immediate current-batch SUMMARY/SCOUTING/discovery alias screen found the exact floor family only in r237. Current arXiv title, author/floor, and Jacobsthal/Tverberg queries return the original 1708.03190v2 only. This is not an exhaustive citing search or public-registry clearance. Previously denied GitHub raw/API/codeload/diff/patch and other blocked historical intervals are parked, with no retry, browser, proxy or TLS bypass. No worldwide priority assertion. Counts remain9/39/next40; root alone decides.
''')
w('SCOUTING.md',r'''# Eight additional original question families; none novelty-cleared

These are eight distinct question-posing families additional to r231/r234/r237 in the bounded immediate-report alias screen. They are NOT eight demonstrated currently open problems. Every URL below is the actual original body, frozen before mathematical reading. Chronology is the body's closing publication line, also retained verbatim in source-chronology.json. No already-solved control is used to pad these eight. Current arXiv queries are in screen-*.xml/extra-*.xml, retrieved Oct30 2026; empty results are a limitation, not clearance. Public-registry/historical inaccessible intervals stay parked. No search of recent resolution announcements was used to select targets.

1. **Braided nonintersecting diagonals.** Boyland–Pintér–Laukó–Roth–Schoenfield–Wasielewski, *On the Maximum Number of Non-intersecting Diagonals in an Array*, published Dec27 2016, Section5 Q1 p23. https://cs.uwaterloo.ca/journals/JIS/VOL20/Pinter/pinter3.pdf . For every positive odd h,w, is D(h,w)=T(h,w), where D is the maximum placement of cell diagonals with no crossing or common endpoint and T is the braided construction? Actual Proposition13 p15 computes T=L+floor((t-2s+2sqrt(t²-st+s²))/3), s=(max(h,w)+1)/2,t=(min(h,w)+1)/2; it optimizes braided constructions, not all placements. Mechanism: row boundary states and a dual charging invariant; next calculation is exact optimality gaps for odd rectangles using the source's braid state. Current primary query finds arXiv:2102.00547v1, *Maximum Number ... Square Arrays*. Its body has NOT been read; even its square scope could invalidate part of the target, so this family is on follow-up hold, not a fresh nomination. This is one placement family, not separate two/three-dimensional credits.

2. **Rational-numerator continued fractions.** Greene–Schmieg, *Continued Fractions with Non-Integer Numerators*, C25–27 p15. https://cs.uwaterloo.ca/journals/JIS/VOL20/Greene/greene3.pdf . Exact manageable target C25: for z=2/3, every positive rational has a finite maximal cf_z expansion, whose iteration takes the integer part then replaces the remaining nonzero fraction by z divided by that fraction. Actual Theorem24 p14 and proof classify period-one rational expansions for rational z by x=(nw+k)/w, z=k(nw+k)/w², positive integers w,k,n, gcd(k,w)=1, maximal when1<=k<w. That does not prove termination at2/3. Mechanism: reduced numerator/denominator descent, tracking cancellation factors2 and3; next derive a height that strictly decreases across a block of steps. Objection: generalized Euclidean algorithms may already subsume it; no full algorithm-literature body screen. Current exact-title arXiv query empty. C26 z=5/3 and C27 z=11/8,x=4/5 are the same family and no extra breadth; a finite long orbit cannot prove aperiodicity.

3. **TRIP-Stern maximal paths.** Amburg et al., *Stern Sequences for a Family of Multidimensional Continued Fractions: TRIP-Stern Sequences*, published Dec26 2016, Q11 p20, Q14/C15 pp22–23. https://cs.uwaterloo.ca/journals/JIS/VOL20/Garrity/garrity6.pdf . Q11 asks for maximal-term paths for the remaining60 of216 permutation-triple TRIP maps; the objects are the binary trees from the source F0,F1 matrices starting at(1,1,1). Do not silently pick one map and claim the classification. Actual Theorem10 proof identifies always-right, always-left or alternating paths for26 representatives and Lemma9 expands to156 maps. Theorems12–13 derive actual recurrences only for covered subfamilies. Mechanism: finite cones of coordinate dominance under paired nonnegative matrices; next generate invariant cones for all remaining representatives and seek a uniform word policy. Objection: joint-spectral-radius phenomena may prevent a simple finite policy. Current primary query returns original arXiv:1509.05239v2, no independent later body inspected. Park pending map inventory and literature comparison.

4. **Iterated Beatty recurrences.** Ballot, *On Functions Expressible as Words on a Pair of Beatty Sequences*, published Jan28 2017, minor revision July30 2017, P38 p22. https://cs.uwaterloo.ca/journals/JIS/VOL20/Ballot/ballot22.pdf . For fixed positive integer k and alpha=(1+sqrt5)/2, a_(n+2)=a_(n+1)+a_n+floor(k{alpha a_(n+1)}), with integer initial data as in the discussion, asks whether these sequences always satisfy homogeneous linear recurrences, what characteristic polynomials occur, and dependence on initial data. The source suggests x²-x-1 or (x²-x-1)(x^h-1), not a proved classification. Actual Lemma17/source Section4 obtains a finite-valued correction in its special Beatty iteration and an extra x^4-1 factor; P38 explicitly asks to generalize that mechanism. Next: derive a bounded fractional-part state map and prove eventual periodicity or construct an aperiodic orbit. Objection: cannot replace bounded correction by periodic correction without proof; integer initial-data range must be reconciled before nomination. Current author/Beatty query finds the original precursor arXiv:1704.04476v1 under a different title, *On a family of recurrences ... Fibonacci ... Narayana*. This alias is retained, not counted as a new paper.

5. **Center index from generalized commuting probabilities.** Cherniavsky–Levit–Goldstein–Shwartz, *Hultman Numbers and Generalized Commuting Probability in Finite Groups*, published Nov22 2017, C72 p51. https://cs.uwaterloo.ca/journals/JIS/VOL20/Levit/levit4.pdf . For any finite groups G1,G2, equality Pr^(2t)(G1)=Pr^(2t)(G2) for EVERY t>=1 is conjectured to imply |G1/Z(G1)|=|G2/Z(G2)|. Pr^(2t) is the source probability a1...a_(2t)=a_(2t)...a1, not pairwise commuting probability. Actual Theorem70 gives limit1/|G'|; Theorem71 gives equality under isoclinism; the following explicit order64 examples disprove the full converse, not C72. Mechanism: character-degree moment reconstruction; next derive exactly which normalized degree multiplicities the entire probability sequence determines and test whether the number of linear characters recovers center index. Objection: already-known character-theoretic formulas may make it routine, or isocategorical examples may refute it. Current primary query finds original arXiv:1403.3868v2 and signed follow-up1906.05522v4. Actual follow-up Theorem5.6 proof pp23–24 classifies signed-permutation probabilities using cycle number and positivity, not the center-index converse. This is bounded noncoverage of that theorem, not clearance of the whole literature.

6. **Alternating exponential-divisor sums.** Tóth, *Alternating Sums Concerning Multiplicative Arithmetic Functions*, Section4.15 OpenP55 p36. https://cs.uwaterloo.ca/journals/JIS/VOL20/Toth/toth25.pdf . Investigate sum_(n<=x)(-1)^(n-1)tau^(e)(n) and its reciprocal-weight version; tau^(e) is multiplicative with tau^(e)(p^nu)=tau(nu), tau^(e)(1)=1. The precise next subgoal is a two-term asymptotic with a justified error, not an assertion that computing a mean solves all of the open-ended P55. Actual preceding source limit already gives A1(2/(1+K)-1), K=sum_(nu>=1)tau(nu)/2^nu, so that leading-mean result is a solved control and excluded. Mechanism: isolate the Euler factor at2 in the Dirichlet series, transfer the known x,x^(1/2) terms through an absolutely convergent convolution, and control tails. Next calculate whether the local factor reciprocal has radius sufficient to retain the source's exponent. Objection: Proposition2 plus classical estimates may yield this routinely; current author/alternating query returns original1608.00795v2 and older survey1111.4842v2. No fresh-resolution inference.

7. **B-sequence composition for Riordan pseudo-involutions.** Phulara–Shapiro, *Constructing Pseudo-Involutions in the Riordan Group*, published Feb18 2017, Q10 p8. https://cs.uwaterloo.ca/journals/JIS/VOL20/Phulara/phulara3.pdf . For a source pseudo-involution D=(g,f) with B-sequence b0,b1,..., determine the B-sequence of D². B-sequence is the source row identity d_(n+1,k)=d_(n,k-1)+sum_(j>=0)b_j d_(n-j,k+j). Actual Corollary5 proves all powers remain pseudo-involutions; Theorem8/proof p7 relates A and B by A(z)=1+zB(z²/A(z)), using the compositional inverse identity. It supplies a mechanism but not an explicit general composition law. Next eliminate f from f(f(z)) and apply exact formal Lagrange inversion to z²/A(z), retaining all coefficients and g admissibility. Objection: a merely implicit recomputation is helper/routine scope, and later B-sequence papers may already provide the law. Current author/involution and pseudo/B-sequence arXiv queries empty, which is particularly weak screening. Hold for broader primary bibliography before solving.

8. **Approximate recurrences for finite spectral alphabets.** Coons, *Extension of a Theorem of Duffin and Schaeffer*, published Sept15 2017, Q2 p3. https://cs.uwaterloo.ca/journals/JIS/VOL20/Coons/coons7.pdf . Let a(n)=sum_(i=0)^M b_(i,n) zeta_i^n, with all b_(i,n),zeta_i in a fixed finite complex set B and |zeta_i|=1. If for EVERY epsilon>0 there exist q>=1 and complex gamma0,...,gamma_(q-1), depending on epsilon, with |sum_(j=0)^(q-1)gamma_j a(n+j)+a(n+q)|<epsilon for EVERY n>=0, must a be linearly recurrent? Actual Theorem1/proof pp1–3 handles spectral arguments in pi*Q via a finite phase alphabet and induction on distinct eigenvalue moduli, invoking the polynomial-coefficient theorem of Tang–Wang. It does not handle arbitrary unit phases. Mechanism: compact torus orbits and uniform separation of finite exponential sums; next test whether arbitrarily small monic annihilators force a fixed annihilator, without assuming bounded q or bounded coefficients. Objection: absence of such bounds may be essential and connects to operator-spectrum problems. Current author/Duffin query finds only original1706.02470v3. Park pending approximation-theory bodies, not fresh priority clearance.

## Controls and ranking
Gavrylkiv Q9 is an exact historical duplicate of r231; excluded. Mangontarum P9 (q,r-Dowling Hankel transform) has close current hits1907.03094v2 and2103.08062v1. The actual first follow-up Theorem4.1 concerns a Whitney-array determinant, not automatically the Dowling moment determinant; no unwritten equivalence is assumed, and this follow-up-contingent family is excluded from the eight. Rubey–Stump paper resolves its cited Dyck-path conjectures in its own proof, excluded. Other downloaded vol20 papers with no actual question located are search negatives, not breadth. Davis width-k and Alm Ramsey questions are reserves only, not padded slots. No ear-triangulations, subsum, centers, Riesz, inverse-period-doubling or Borisov investigation was performed.

Priority: keep the exact floor bound first, now with unbounded UNSAT lead needing independent proof checking. Of the breadth, Riordan has the most concrete coefficient calculation but substantial routine/prior risk; commuting probabilities has a finite character-moment mechanism; rational cf_z termination has a concrete arithmetic descent test but may be much harder. The others remain qualification holds. Eight original families are documented; ZERO are novelty-cleared or acceptance-ready, so there is a complete shortfall of eight if 'fresh breadth' is interpreted as eight currently-open, fully qualified nominations.
''')
w('SUMMARY.md','''# r241 research handoff

No ordinary full-source proof or counterexample is claimed. No PROOF.md is issued. Counts remain **9 additional /39 total /next40**; root alone accepts/counts.

The exact all-parameter four-variable lower bound is explicitly independently conjectured on Wong p15, not merely an unasked fragment of C17. Actual 2017 Theorem9 proof has now been read and does not subsume it. The live publisher PDF matches the frozen r237 original.

Main advance: exact residue-preserving reduction to finite integer piecewise linear arithmetic. The unbounded counterexample query returns UNSAT twice, including a proof-producing replay. The emitted Z3 proof is **not independently checked**; no solver output is promoted to an ordinary proof. See discovery.md, all-m-query.smt2, lia-result.json and proof-object-status.json. Finite diagnostics through m24 are separate.

SCOUTING.md documents eight additional original source-question families, exact scopes, closest source results, mechanisms and bounded historical/current screening. None is novelty-cleared; solved/duplicate/follow-up controls do not pad the eight. A full qualification shortfall is explicitly retained.

No shared/git/public/browser/MathDB/Lean/manuscript edits. All executable work used the mandated guard/caps. Final manifest excludes itself and verification receipt; final verification runs separately.
''')
w('progress.md','''1. Administrative context snapshotted; count9/39/next40 reconciled; ancestor and batch rules read.
2. r237 SCOUTING and original Wong sources frozen/hash-checked before scientific reading.
3. Exact source scope and 2017 predecessor proof read; current floor author/title/alias queries performed.
4. Quotient/remainder and cyclic cancellation routes derived; all-boundary integer-linear counterexample encoding created.
5. Exact finite checks m1..24 pass. Default and proof-producing unbounded SMT runs return UNSAT; independent certificate checking remains open.
6. Eight distinct extra original families screened with objections; no nomination or count claim.
7. Source bindings checked after reading and final packet written; separate guarded verification follows.
''')
w('failures.md','''# Preserved failures and limits

Three HTTP404 attempts are preserved in failures.jsonl: two incorrectly guessed JIS index paths and an accidental invalid 'https-no' batch argument. The actual index was then discovered from the publisher home-page link. No denied route was retried. No403/429/challenge encountered here; previously denied GitHub/ScienceDirect/Google challenge routes were not accessed. Historical inaccessible public-registry intervals remain parked; no HEAD loop or alternate transport bypass.

Initial z3 import failed (lia-initial-failure.json). z3-solver5.3.3.0 was subsequently installed only inside this lane under the same guard/caps. The failed attempt is retained. Two successful UNSAT runs followed. The proof object is not independently checked and supplies no ordinary-proof claim.

Index pages were hashed on retrieval before reading, but initial publisher home-page/volume index copies were made at finalization rather than before reading. Mathematical PDF bodies were copied and hashed before text extraction/reading. This sequencing limitation concerns navigation indexes; it is not hidden as strict pre-read-copy compliance.

Finite minima do not imply a universal inequality. Continuous optimization alone would lose m modulo3 corrections. Cyclic identities do not by themselves prove the bound. No certified chamber enumeration, independent proof-object checker, global prior-art clearance, Lean or manuscript is supplied.
''')
chron={}
for name in ['greene3','pinter3','garrity6','ballot22','levit4','toth25','phulara3','coons7','pong11','wong-current']:
 t=(L/'sources'/(name+'.txt')).read_text();i=t.rfind('Received');chron[name]={'closing_publication_passage':t[i:i+650],'pdf_sha256':h(L/'sources'/(name+'.pdf'))}
w('source-chronology.json',chron)
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
w('provenance.json',{'lane':str(L),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'counts':{'additional':9,'total':39,'next':40},'root_only_acceptance':True,'guard':{'path':str(guard),'sha256':h(guard),'AS_bytes':536870912,'groupRSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'cap_raises':False},'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'source_bindings':'scientificbindings.json','current_queries':'retrieval.jsonl','history':'history.json','ordinary_proof':False,'solver_proof_independently_checked':False,'external_writes':False,'initial_index_copy_sequence_limit':'failures.md'})
manifest={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
w('manifest.json',manifest)
print({'files':len(manifest),'proof_object':json.loads((L/'proof-object-status.json').read_text())})
