# Independent adversarial proof review: complete graph minus one edge

**Verdict: PASS for the full Theorem A and Corollary B, under the explicitly stipulated pinned upstream mathematics. No required mathematical repair identified.**

The reviewed candidate is `../fresh-substantial-discovery-r2/candidate.md`, all 182 lines, 23,029 bytes, SHA-256 `2a078a07142986c93845f4855496db14e41ee2590adc17720727b19145dd1c8b`. This verdict is an independent proof review, not a contribution, manuscript, formalization, campaign-acceptance, or priority decision. The frozen candidate was not edited. Nothing was staged, committed, submitted, uploaded, or sent to another person; no agents were spawned and no campaign count was changed.

Review artifact author: **Myeongjin Kang**, no affiliation. Original review prose: CC BY 4.0; original review code: MIT. Third-party material retains its authorship and rights. The reviewing agent is GPT-6.1-Sol/high; this record does not attribute upstream results to the reviewer or to the user.

**1. Scope and authentication.** Theorem A concerns ordinary point-count crossing number over all admissible continuous-arc drawings of every `K_n-e`, every integer `n>=2`, every choice of the removed edge. Corollary B concerns `K_m square P_n`, every `m>=4`, `n>=1`, with `P_n` a path of **n edges**. Neither conclusion is restricted to straight-line or two-page drawings. The general lower-bound argument uses a normalized minimum drawing and therefore bounds every drawing. Two pages enter only the upper construction.

Both supplied manifests were parsed and every size and SHA-256 checked: 24 input entries and 9 output entries, all matching. The candidate hash also matches the value specified in the review brief. A fresh HTTPS download of the pinned complete-graph `build/main.tex` matches the frozen 40,122-byte file, SHA-256 `5ae2c60704054f1b45290463c038c32335cc1554c5cc7dcee53518a045472301`. Its Git blob SHA-1 is `826c79722317e701a7c77e9dcc0bb5e082f2bc39`, matching the exact entry in `sources/preprints-tree.json`. See `checks/authentication.json` and `sources/upstream-authentication.json`.

**2. Source interfaces.** I read the actual pinned `main.tex`, not just the supplied source contracts. The mathematical truth of the pinned results is assumed, as authorized; the following checks concern their interfaces.

- U1, `lem:normalization`, lines 850–854, explicitly applies to every finite simple graph and yields a minimum polygonal drawing without crossings of adjacent edges. Independent edges may cross repeatedly. It applies to `K_n-e`.
- U2, `eq:J`, lines 193–232, defines the skew bilinear form on a finite simple graph's real oriented edge space. The proof explicitly states its graph-general scope at line 237. Hence its cycle-vanishing assertion can be applied directly to the graph with the edge absent. The candidate does not substitute the complete-graph form for the deleted graph's form.
- U3, `lem:weights`, lines 362–369, gives zero weighted sums for degrees at most `N-2` on arbitrary distinct real nodes. With `N=n`, it applies to each separate exponent used to make cycles. With the vertex omitted, the relevant node count in the detector is `2s`.
- U4, `eq:M`, lines 427–445, permits any prescribed linear order, independent of numerical node order, and asserts nonsingularity on the **two full rectangles** `P_(s-1,s-2) x P_(s-2,s-1)`. The new proof needs precisely this full statement, not only the subsequent smaller-space detector consequence. Its use is valid for `s>=2` and exactly `2s` nodes.
- U5, `thm:main`, lines 117–126, gives the ordinary crossing number of every complete graph with `n>=3`. The even proof uses it for drawings that need not themselves be good or minimum. A crossing-number lower bound still applies to those drawings.
- U6, lines 720–767, specifies the endpoint-sum page rule, one crossing for same-page alternating independent pairs, and total `Z(n)`. These are exactly the construction facts used in the candidate.

The upstream source does not state a `K_n-e` theorem. Its complete-graph injectivity and isotropy lemmas have not been assumed to extend automatically; the changed steps are audited below. The bipartite companion is not a premise of this new proof. The stipulated truth of the upstream geometry and detector is not re-audited here.

**3. Lemma 3.1: missing-edge cycle tests.** Let `V=P_(n-2,n-2)` and `phi(A)=A(t_a,t_b)-A(t_b,t_a)`. This is a nonzero linear functional: `phi(x)=t_a-t_b != 0`. The two polynomial identities imposed on `H` say exactly that it lies in the kernels of `phi tensor id` and `id tensor phi`. A basis of `V` consisting of one vector of phi-value one and a basis of `ker phi` shows that their intersection is `(ker phi) tensor (ker phi)`. This is a finite-dimensional tensor calculation, with no implicit evaluation-to-polynomial inference.

For each `A` in this kernel, the coefficient of the oriented missing basis edge in the complete-pair chain is exactly

`w_a w_b (A(t_a,t_b)-A(t_b,t_a))=0`.

There is no additional factor two here: the two ordered endpoint terms have opposite oriented edge vectors. The chain therefore belongs to the actual edge space of `G`. For every rectangular monomial the boundary is the difference of two products, each containing a zero barycentric sum. Thus it is a cycle of `G`, not merely a chain whose boundary vanishes before deleting an edge. U2 gives the asserted identity, and zero extension of J on the absent pair is precisely the bilinear coordinate extension of this identity. All steps are valid.

**The hypotheses are sufficient, not a characterization of all zero tests.** For example `H(x,u,y,v)=xy` violates both missing-pair polynomial identities when `t_a!=t_b`, yet its pairing always vanishes: it pairs the same zero-extended chain with itself in a skew form. Thus no converse follows from the author's generic negative controls. The remark at candidate line 66 can validly be read as “the assumptions cannot simply be dropped in general”; it must not be strengthened to an if-and-only-if claim. This is a clarification of scope, not a repair needed by the proof.

**4. Lemmas 3.2–3.3: spaces, orientations, and mixed orthogonality.** A symmetric polynomial in one pair of separate degree at most `s-2` has dimension `d=binom(s,2)`. Evaluating its first pair at `(t_a,t_b)` is a nonzero scalar functional, and the evaluation `S -> symmetric(y,v)` is onto by taking polynomials independent of `(x,u)`. Thus `dim S_a=dim S_b=d(d-1)`. The edge-slot swap identifies the two kernels.

For `P in S_a`, `Q in S_b`, the test `PQ Delta` has separate degrees at most `2(s-2)+3=2s-1=n-2`. At the first missing-pair substitution it vanishes through P, and at the second it vanishes through Q, in either endpoint order. Repeated vertices kill Delta; absent edges kill J. Consequently the cycle-test identity reduces to the stated supported independent-edge sum.

There are **four** choices of endpoint orientations for a fixed ordered pair of undirected edges. Reversing either edge negates both J and Delta, preserving their product. Division by four is correct. Exchanging the two entire edge slots gives a different coordinate: Delta is unchanged by this even permutation, whereas J changes sign. Accordingly the paired coordinates have diagonal coefficients `a,-a`. This is a nondegenerate **symmetric diagonal form**, not the skew form J, and no coordinate has been counted twice within a single ordered coordinate.

Every diagonal coefficient is nonzero by the definition of T, distinctness of the four labels, and nonzero barycentric weights. The assertion is **mixed orthogonality** `E(S_b) subset E(S_a)^perp`; it does not require either image to be totally isotropic or require their sum to be direct. Both the degree/test step and the linear-algebra interpretation are correct.

**5. Lemma 3.4: the twisted detector.** For each admissible `B'`, the defining pairing depends on the product of its two polynomial arguments. Hence

`M(A,(v-t_a)B') = M(B',(v-t_a)A)`.

The first argument on the right runs over the full rectangle `P_(s-1,s-2)`. The second belongs to `P_(s-2,s-1)`, because `A` has degrees at most `(s-2,s-2)`. Nonsingularity of U4 therefore forces `(v-t_a)A=0` as a polynomial. The real polynomial ring has no zero divisors, so `A=0`. This is not an argument that evaluation multiplication by `v-t_a` is invertible at the nodes: it is not invertible there. Polynomial nonsingularity on the stated rectangles is what makes the twist valid. No strengthening of U4 is being assumed.

**6. Lemma 3.5(a): localization and interpolation.** The complete test has separate degree bounds

`x: (s-2)+1+s=2s-1`,

`u: (s-2)+2+(s-1)=2s-1`,

`y: (s-2)+1+1+(s-1)=2s-1`,

`v: (s-2)+2+1+(s-2)=2s-1`.

All extra missing-edge factors have been paid for. The first missing-pair tests vanish through `P in S_a`. The second-slot substitution `(a,b)` vanishes through `(y-t_a)`; the reverse substitution `(b,a)` vanishes through `(v-t_a)`. Thus both are polynomial identities, even though the test need not be within-pair symmetric.

An independent pair contributes zero by the assumed evaluation kernel, or by J being zero. Loops and the absent pair also contribute zero. For adjacent edges the factor `(u-v)(u-y)(v-x)` kills the coincidences `p=q`, `p=k`, and `q=i`. The only surviving case is `i=k` with the other three indices distinct. At such a term the factor is

`(t_p-t_q)(t_p-t_i)(t_q-t_i)`.

There is no hidden minus sign. Since `F'(t_p)=(t_p-t_i)F_i'(t_p)`, the weight transformation gives exactly the order pairing claimed at candidate line 111, multiplied by `w_i^2 U(t_i)(t_i-t_a)V'(t_i)`.

For `i` outside `{a,b}`, every spoke exists; adjacent edges have no interior crossings and both chosen edge orientations point out from i. Hence their J-value is the full `S_i(p,q)=T_i(ip,iq)/2` on all `2s` other nodes, with the arbitrary rotation order allowed by U4. At `i=a,b` this need not be a full order matrix. The proof does not claim it is. Define their inner sums directly with the zero-extended J, and leave them uninterpreted.

For fixed `B'`, the identities hold for every U and V'. Linear combinations of their products span all univariate polynomials of degree at most `s+(s-1)=2s-1`. Multiplication by `(t-t_a)` therefore supplies every polynomial of degree at most `2s` vanishing at `t_a`. In particular it supplies the Lagrange polynomial isolating any `i_0` outside `{a,b}`. That polynomial also vanishes at `t_b`. Both incomplete stars disappear, and the surviving coefficient `w_(i_0)^2` is nonzero. The polynomial first argument of M has degrees at most `(s-2,s-2)`; the node `t_a` is among the `2s` remaining nodes. Lemma 3.4 now gives the required polynomial identity at each of the `n-2` complete stars. This is the critical changed step, and it is sound.

**7. Lemma 3.5(b,c): roots, division, descent, and the other slot.** After substituting `y=x`, the x-degree is at most `2s-4`. Its coefficients in `(u,v)` vanish at `n-2=2s-1` distinct x-values. The coefficientwise univariate root bound gives the polynomial identity `P(x,u,x,v)=0`, so `x-y` divides P. The within-pair swaps give divisibility by `x-v`, `u-y`, and `u-v`. These four linear factors are pairwise nonassociate primes in the polynomial ring, so their product C divides P.

For nonzero `P=CR`, separate degrees add in each variable, giving `deg_z R=deg_z P-2`. C is invariant under both within-pair swaps; cancellation in the integral domain transfers these symmetries to R. Crucially,

`C(t_a,t_b,y,v)=(t_a-y)(t_a-v)(t_b-y)(t_b-v)`

is a nonzero polynomial in `(y,v)`. It need not be nonzero at every point, and the argument does not need that. Cancelling it from the polynomial identity for P proves `R in S_a`. C is nonzero at every evaluated independent pair, so `E(R)=0`. A nonzero kernel element of minimum x-degree would therefore give one of smaller x-degree, a contradiction. There is no loss of the missing-pair condition on descent.

For `s=2`, `S_a=S_b={0}` already. For `s=3`, every separate degree is at most one, so divisibility by C is impossible for a nonzero polynomial; no polynomial space with a negative degree bound needs to be formed. More generally, whenever any separate degree is less than two, the factorization itself proves P zero. In the remaining cases the quotient has nonnegative degrees and the descent applies. Thus the compressed small-degree language at candidate line 114 hides no exceptional case.

The support T is closed under swapping its two undirected edges because J is skew. The slot swap sends `S_b` isomorphically to `S_a` and permutes the evaluation coordinates. This proves injectivity on `S_b` without assuming anything about missing-endpoint orders or repeating an asymmetric argument incorrectly.

**8. Proposition 3.6 and unrestricted drawings.** A nondegenerate bilinear form on the whole coordinate space gives `dim W_a^perp=|T|-dim W_a`, whether or not its restriction to `W_a` is nondegenerate. Mixed orthogonality and the two injectivities consequently yield `|T|>=2d(d-1)`. A supported unordered independent pair requires at least one actual crossing, while T records both orders. Thus `c(D)>=|T|/2>=d(d-1)`. Repeated crossings and cancellation of signed intersections cannot invalidate the support bound: cancellation removes support, and multiple crossings only increase the actual crossing count. U1 applied to a minimum ordinary drawing transfers this bound to all ordinary drawings. No two-page, rectilinear, or single-crossing-per-pair assumption enters the lower bound.

**9. Even n: insertion and subtraction.** I independently checked candidate lines 125–136, including the construction in the retained primary OWH text. In a normalized drawing, `x-v_i-y` is a simple path. A sufficiently thin parallel track follows each of its two arcs through its existing crossing disks, meets every old edge once for each original path-edge crossing, and joins around `v_i` inside a small disk. The join crosses exactly `m_i` other spokes there. It can avoid the two followed spokes, all other vertices, and itself. Generic local choices prevent triple crossings. Thus the inserted edge is an admissible simple arc and adds exactly `a_i+m_i` crossings. It may cross an edge incident to x or y; the resulting complete-graph drawing need not be good. This causes no problem.

For the original normalized D, crossings have four distinct endpoints. A core–core crossing is counted twice by `c(K^x)+c(K^y)`, a star–core crossing once there and once in `sum a_i`, and an x-star–y-star crossing twice in `sum a_i`. This proves `2c(D)=c(K^x)+c(K^y)+sum a_i` with all multiplicities correct.

The responsibility calculation uses `sum_v r_D(v)=4c(D)` only in D. At `v_i` in `D_i`, the old spokes still do not cross each other, and the only new crossings incident to these spokes are the `m_i` local ones. The inserted edge is xy, not an edge incident to `v_i`. Therefore

`r_(D_i)(v_i)=r_D(v_i)+m_i=c(D_i)-c(D_i-v_i)`

holds even when `D_i` has adjacent-edge crossings elsewhere. The subdrawing after deleting `v_i` is still an admissible drawing of `K_(n-1)`, so U5 bounds it below. Both (4.1) and (4.2) follow with the signs given.

For explicit inequality direction, write their common portion as `B=(n-2)Z(n)-nZ(n-1)-(l_1+l_2)+sum c_i-sum m_i`. Equation (4.2) says `2c(D)<=B`, so `nc(D)-2c(D)>=nc(D)-B`. Substitute (4.1) on the right to obtain

`(n-2)c(D)>=(n+2)Z(n-1)+2(l_1+l_2)`.

All `m_i` cancel; no estimate on them is needed. For `n=2M>=6`, inserting `Z(2M-1)=(M-1)^2(M-2)^2/4` gives `(M^2-1)(M-2)^2/4`, the claimed even target. Thus this part is a valid re-derivation of the literature consequence.

**10. Matching upper bound and small cases.** In U6 remove edge `{0,t}`, `t=floor((n-1)/2)`. Its possible crossings are exactly edges `0<i<t<j<n`. For `n=2s+1`, its page is the residue interval `[s,2s]`, and a competing edge has that page exactly when `i+j<=2s`; the count is `sum_(i=1)^(s-1)(s-i)=binom(s,2)`. For `n=2s`, its page is `[0,s-1]`, the condition is `i+j>=2s`, and the count is `sum_(i=1)^(s-2)i=binom(s-1,2)`. The modular wraparound does not add a second qualifying interval in either of these specified ranges. Removing the edge removes exactly these crossings and gives the lower-bound value.

For `n=2,3,4` the values are zero and the graphs are planar; for `n=5` deleting the indicated edge from U6 leaves zero crossings. The floor product, binomial expression, and both parity expressions agree, including these zero cases. Edge transitivity of `K_n` then covers any specified e. Theorem A has the full stated scope.

**11. Corollary B: exact primary-literature interface.** I read the retained publisher full-text extraction, not merely the CHN survey: `sources/literature/owh-2014-sciencedirect-fetch.txt` in the frozen directory, authenticated SHA-256 `69b46e0f623ae186f258a2108466c8ecce4f58e6b7e8aa54d68f2520561878ba`. The primary publication is [Ouyang–Wang–Huang, Discrete Mathematics 328 (2014), 71–78](https://doi.org/10.1016/j.disc.2014.03.011).

At extraction line 264, P_n is defined to have vertices `0,...,n`. Lines 286–300 give an upper theorem for vertex-transitive G and a lower theorem for G with four dominating vertices. `K_m` satisfies both hypotheses for every `m>=4`. Lines 308–314 state and derive Corollary 5.1 for all `m>=4,n>=1`, using `K_m+2K_1 = K_(m+2)-e` and `K_m+K_1=K_(m+1)`. It is **unconditional**. Its proof does not assume Harary–Hill or the conjectured deletion formula. Those appear in other statements, including conditional Corollary 5.3, which is not being substituted for Corollary 5.1.

Accordingly the candidate may cite the published corollary normally; no new proof of its zip-product machinery is required for this review. This checks its exact interface, not a re-audit of every cited published argument. Fresh access attempts to ScienceDirect returned HTTP 403, recorded in `sources/owh-live-status.txt`; the retained primary text supplies the actual statement and definitions. I do not claim a successful independent live fetch of the OWH full text.

Substitution gives, for `m=2k`,

`k(k-1)^2 [n(k+2)+k-2]/4`,

and for `m=2k+1`,

`(k+1)k(k-1) [n(k+2)+k-2]/4`.

These agree with all the floor factors in Corollary B, respectively. The endpoint `n=1` cancels the deleted-graph term and gives `2cr(K_(m+1))`; `m=4` gives `2n`. There is no missing path vertex shift or unexposed conditional dependency.

**12. Computational audit and adversarial support.** Both author scripts and both retained outputs were read in full. The author's stdlib checker was rerun with bytecode disabled from this review directory; every result line agrees with the frozen output, apart from the latter's extra shell timing lines. Its exact rational identities and sampled orthogonality pass. Its rank checks are modular, even in the nominally “exact” script, and its generic invalid-test nonzero values are printed rather than asserted. Its random straight-line geometry uses floating points and `atan2`. These are limits of finite support, not assumptions of the proof.

I also audited the larger NumPy checker without rerunning its entire 18-minute run. For `p=2^31-1`, every fixed-width product is below `(p-1)^2<2^62`, reductions occur before accumulation, and the additions/subtractions remain within signed 64-bit range. There is no unbounded NumPy dot product. The displayed node differences are nonzero modulo p, as are the rational denominators used. The missing-pair kernel equations have constant pivot one, so their modular bases are reductions of integral bases. Thus full modular rank is legitimate evidence for these particular rational evaluation matrices. Modular orthogonality alone remains only a necessary finite condition, and the script states this limit.

`checks/adversarial.py` is independent code and imports no author helper. It uses exact integer orientation predicates, exact rational crossing coordinates, an exact half-plane/cross-product rotation sort, checks against triple crossings, and shuffled real labels unrelated to geometric order. Its final run passes:

- rational missing-pair and local factor identities at `n=7`, with each of the two twist-factor omissions producing a nonzero test;
- analogous modular checks at `n=15`, including a generic invalid test with nonzero value;
- the universal nonconverse example `H=xy`, checked in both cases;
- twice-J sign and barycentric local-weight equalities term by term, including absent spokes;
- event-sign controls replacing one crossing by three of the same total sign: crossing count rises from 26 to 28 and 965 to 967 while signed support stays unchanged;
- a twisted detector at `s=7`, 14 arbitrarily ordered nodes, every one of the 14 twist nodes, rank 36;
- an independently built tight two-page support at `n=15`, 840 ordered coordinates, rank 420 on `S_a`, rank 420 on `S_b` via checked coordinate swap, and 100 mixed orthogonality pairs;
- a fresh rank calculation after deleting one independent basis row, rank 419, establishing that the rank test is responsive;
- floor/product/corollary identities and even-counting models including arbitrary multiplicities.

The three-crossing event control is a consistency check of signs and counts, not a numerical reconstruction of a polygonal wiggle. The local-disk geometric argument justifies that operation. Full-rank modular evidence concerns only the finite matrices, and modular zero tests are not exact rational certificates. None supplies the all-n proof; Sections 3–11 above audit that proof separately.

Early reviewer-control runs incorrectly demanded that specific invalid tests always be nonzero. At `n=15` the initially chosen missing edge had no crossings in the corresponding full straight-line drawing, and several such tests vanished. Even with a crossed deleted edge one particular omitted-factor test still vanishes. The raw early failure logs are retained. The final checker distinguishes observed zeros from nonzero controls and includes the analytic `H=xy` counterexample to any converse. These were faulty expectations in the review harness, not counterexamples to Lemma 3.1 or to the theorem.

**13. Boundaries and formalizable core.** The exact routine-range arithmetic is consistent with the candidate: the OWH 3.1 deficit for `n=2s+1` is `(s-1)(s-2)/(2(2s+1))`. It is less than one for `2<=s<=6` and at least one for `s>=7`, since numerator minus denominator is `s(s-7)`. Hence the listed counting-plus-integrality route stops at odd n=13. This only identifies what that route proves, not literature priority. Even cases are credited consequences of OWH and upstream Harary–Hill. The odd all-n bridge has been independently checked here, but this verdict does not certify substantiality or novelty.

A natural formalizable core consists of the tensor-kernel lemma, the rectangle multiplication/detector implication, separate-degree and missing-pair evaluation identities, coefficientwise root counting, collision-factor division and kernel descent, the mixed-orthogonal dimension bound, and the two parity simplifications. A complete formalization would additionally need the drawing/edge-chain infrastructure and explicit upstream assumptions. **No Lean certificate has been produced or checked in this review.**

There are no outstanding mathematical objections requiring a narrowed theorem or repaired frozen proof. The upstream assumptions and normal citation of the published product identity remain explicit. Parent contribution and manuscript gates, formalization work, acceptance decisions, and public actions remain outside this review.
