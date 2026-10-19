# Arithmetic/algebraic discovery r78: pre-freeze research archive

Myeongjin Kang; no affiliation. Original prose, 2026-10-18. This is a research archive, not a nomination or a contribution/count/gate decision. No candidate was frozen. All calculations below preceded the decision not to freeze a candidate. No frozen scope has been changed, and no limited repair is offered in place of a full result.

The stipulated source revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its theorem statements **and operative proof operations** are inputs, not objects of truth-audit. The three sustained investigations were families 055, 206, and 210. Family 057 received source-operation and actual historical-proof comparison; 202 was excluded from actual project history before fresh operative proof research. These five are not five equally researched families. Catalogue/history navigation through 019/020/029/031 is not counted as operative research.

## 1. Finite covers and the numerical support interface (055)

### Source operations and closest previous work

The pinned prescribed-large-volume manuscript supplies `thm:geometric-sector`: on every smooth connected projective complex threefold with trivial canonical bundle, its specified large-volume charges give geometric stability conditions throughout a real divisor sector with a uniform large-volume threshold. Its `prop:exact-double-tilt-heart` identifies the **ordinary**, non-Todd charge heart with the physical double tilt, including zero-slope boundaries. This is stronger for descent purposes than merely knowing that some stability condition with a desired central charge exists. The ordinary charge is

\[
 Z_{B,tH}(E)=-\operatorname{ch}_3^B(E)+\frac{t^2}{2}H^2\operatorname{ch}_1^B(E)
 +i\left(tH\operatorname{ch}_2^B(E)-\frac{t^3}{6}H^3\operatorname{ch}_0(E)\right).
\]

The source has full numerical support on the covering threefold. Its separate Todd-charge construction is not silently assigned the ordinary heart. The source Gepner companion already proves its normalized exact Gepner relation and periodicity on every smooth quintic. Arithmetic r9 actually studied a path from this condition to large volume and found failure of a particular standard quadratic-form route; that is neither a general disconnectedness theorem nor an unpaid continuation construction. We did not reopen it.

The strongest compatible primary operations are the following, read in their proof bodies:

* Macrì–Mehrotra–Stellari, [*Inducing stability conditions*, arXiv:0705.3752v3](https://arxiv.org/pdf/0705.3752v3), §2.3, Lemmas 2.15–2.16 and Proposition 2.17: invariance allows the unique Harder–Narasimhan triangles to acquire coherent linearizations. Forgetting and inflation induce the stability condition; their composite multiplies charge by the group order. Remark 2.18 expressly factors the numerical map through invariant numerical classes.
* Bayer–Macrì–Stellari, [arXiv:1410.1585v2](https://arxiv.org/pdf/1410.1585v2), Proposition 6.1: finite étale pullback preserves and reflects the first tilt heart and tilt semistability, by descent of the unique destabilizing HN subobject. Section 10, Theorem 10.1 and its proof, already performs equivariant stability induction with a lattice defined by forgetting. Examples include smooth quotients with torsion canonical bundle.
* Dell–Heng–Licata, [arXiv:2311.06857v2](https://arxiv.org/pdf/2311.06857v2), Appendix A, especially its concluding induction construction: the support property is retained relative to the **induced lattice and induced class map**. This does not identify that lattice with every numerical direction of the equivariant category.

### Feasibility calculation: the smooth torsion-canonical route closes by these operations

Let X be a smooth connected projective complex threefold with K_X of exact finite order m. Its canonical cyclic cover p:Y→X is finite étale of degree m with K_Y trivial; using exact order gives the connected cover. For pullbacks of real B and ample H, the source's ordinary double-tilt heart and central charge are invariant under the deck group. The primary HN construction therefore gives a stability condition on X. Both tilts agree with the ordinary tilts on X: uniqueness descends the slope HN filtration at the first step and the tilt HN filtration at the second. This also explains why one must use the source's exact heart operation, rather than average an unspecified heart.

The charge calculation is exactly

\[
 Z_{p^*B,tp^*H}^{Y}(p^*E)=mZ_{B,tH}^{X}(E).
\]

After dividing the induced charge by m, it is the prescribed ordinary charge on X. Full numerical support introduces no new obstacle in this free-cover case. Pullback and pushforward descend to numerical Grothendieck groups by their Euler-pairing adjunctions. The identity

\[
 p_*p^*[E]=[E]\sum_{j=0}^{m-1}[K_X^{-j}]=m[E]
 \quad\text{in }K_{\rm num}(X)_\mathbb R
\]

uses numerical triviality of torsion line bundles, which follows from Hirzebruch–Riemann–Roch. Thus p* is injective. For chosen finite-dimensional norms there is a constant c_p with ||v||≤c_p||p*v||. At each allowed parameter, if the covering support constant is C_Y, then for a semistable class

\[
 \|v\|\le c_p C_Y m|Z_X(v)|.
\]

The dependence here is on the fixed cover, norms, and covering stability condition. No parameter-uniform support constant as t→∞ is inferred. The source's uniform **threshold** does descend: take the inverse images of its open real divisor sectors under p*, and use its threshold there.

Finally p*O_x is the sum of the m distinct point objects over x, all stable of the same phase upstairs. A subobject of this sum in that phase category is a sum of some of the distinct simple summands. Equivariance makes that subset deck-invariant; the fiber is transitive. Consequently the induced point object is stable downstairs. Its normalized charge is −1. All of this is a compatible application of the actual source heart, primary HN descent, and the elementary numerical left inverse. It supplies no additional operation to nominate. The calculation was not converted into a candidate freeze or a manuscript.

### The nonfree quotient route does not close

For a nonfree finite group action on Y, write q:K_num^G(Y)_R→K_num(Y)_R for the forgetting map. The induced charge factors through q. A support estimate upstairs bounds ||q(v)|| for semistable equivariant objects. It does **not** bound ||v|| merely by finite-dimensionality when q has a kernel. Pulling back a support quadratic form gives Q(q(v)), which vanishes on ker q inside the charge kernel; that form is not negative definite there. The étale left inverse used above is absent.

The strongest primary construction checked here still uses the induced lattice. The missing step for a full-numerical proposal is a bound on the kernel components of **actual semistable equivariant classes**, compatible with the relevant sector and induced heart. We obtained no such bound. This is a limitation of this proof route, not a counterexample to existence or to full numerical support. Indeed a point with a finite group action is a useful safeguard: its semisimple representation category has a dimension charge bounding positive simple multiplicities, despite a noninjective forgetting map. Kernel noninjectivity alone is not a no-go theorem.

No arbitrary quotient, crepant-resolution, Todd-heart, or full-numerical extension was frozen. We neither identify an ordinary numerical lattice with its quotient nor use a weak support result as a substitute.

## 2. Whole intermediate-field lattices over Q (206)

### The arithmetic compatibility to test

The concrete screened question was recognition, from a complete finite lattice order table L, of whether L is the **entire** intermediate-field lattice of some finite extension E/Q. It is important to fix Q, retain all intermediate fields, and keep the order reversal in Galois correspondence. A reduction using arbitrary finite groups would run into an inverse-Galois interface; it would not justify this question just by saying “apply Galois correspondence.”

The actual source eliminates that interface. Its `t:weighted-template` gives literal intervals

\[
 F=[S_Z\times Y,S_{Z\sqcup\bigcup T}],\qquad |Z|>|\bigcup T|.
\]

The top group is already the full symmetric group on the indicated letters. The source `n:circuit-template` computes t_S(C) from the syntax of a positive circuit C using an absolute stock S. A solution determines a literal weighted template F with that many units. Its source `n:template-bound` bounds |F| by a total computable Φ(t), independent of all numerical sizes and the foundation. Finally `t:weighted-realization` gives, from **any** ordinary realization of a nontrivial weighted image with top order M and in either orientation, a common positive size reading bounded by M. The equal-total and square readings hold in the same alignment. The entire template is an allowed image.

This is the strongest relevant source interface, not merely a statement that arbitrary group intervals are undecidable. The arithmetic operation must be compared with it.

### Explicit symmetric realization, with no arbitrary inverse-Galois assumption

For N≥3 choose three distinct sufficiently large primes. Over the respective finite fields prescribe monic squarefree polynomials of degree N with factorization types

\[
 (N),\quad(N-1,1),\quad(2,1,\ldots,1).
\]

Irreducible polynomials of the required degrees exist, and the large primes supply enough distinct linear factors. The Chinese remainder theorem realizes their coefficients by one monic f∈Z[T]. Its irreducible reduction at the first prime makes f irreducible over Q. Dedekind's factorization theorem gives an (N−1)-cycle and a transposition in its transitive Galois group G≤S_N. The stabilizer of the point fixed by that (N−1)-cycle is transitive on the other points. Transitivity of G therefore makes G doubly transitive. Conjugating the transposition gives every transposition, so G=S_N. N=1,2 are immediate.

The actual author-written proof of the factorization theorem was read in Keith Conrad's [*Galois groups over Q and factorizations mod p*, Theorem 1](https://kconrad.math.uconn.edu/blurbs/gradnumthy/galois-Q-factor-mod-p.pdf): distinct roots remain distinct modulo an unramified prime, and Frobenius acts in cycles whose lengths are the irreducible degrees. Conrad's [*Recognizing Galois Groups S_n and A_n*](https://kconrad.math.uconn.edu/blurbs/galoistheory/galoisSnAn.pdf) was used only for its S_n criteria and permutation-group proof; the shorter double-transitivity argument above makes the criterion used here explicit. These are contemporary expository proofs of classical results, not a claim to have read Dedekind's historical original.

Given H≤S_N, choose the resulting Galois extension K/Q and set E=K^H. The **full** field lattice between Q and E is F^op when F=[H,S_N]. No normality of H is needed, and no additional intermediate fields escape Galois correspondence.

### Exact bounded-witness reduction

Positive arithmetic witnesses are recursively enumerable. Enumerate monic irreducible polynomials f over Q and certificates giving deg f distinct Q-automorphisms of K=Q[T]/(f), each by the polynomial image of T. Their validity is checked by exact arithmetic modulo f. Since every root image is present, K/Q is Galois. Compute the finite multiplication table of its automorphisms, enumerate subgroups H, and output the complete interval [H,G]^op. Conversely every finite number field E has a finite Galois closure K/Q, and a primitive integral generator of K eventually occurs with its complete automorphism certificate. Thus this enumeration exhausts the desired field lattices. It requires no efficient Galois algorithm.

Suppose a decision oracle for the screened field-lattice property existed. For each n, enumerate all finite lattice tables with at most n elements and ask the oracle about each. For every YES table run the positive witness enumeration until a witness appears. There are finitely many YES tables and each search terminates. The maximum Galois degree |G| of these witnesses, with 1 as default, gives a total computable bound B(n) under the hypothetical oracle algorithm. Isomorphism checking of finite tables is finite.

Given a positive circuit C, compute n=Φ(t_S(C)). If C is solvable, its source literal template F has |F|≤n. Since its top is symmetric, F^op is an affirmative arithmetic table. It therefore has some Galois realization [H,G]^op with |G|≤B(n). Reversing its field lattice produces an ordinary realization of F. The source's simultaneous weighted reading and `n:circuit-template` give a positive solution of C with all value variables ≤B(n). Conversely, testing all assignments up to B(n) never accepts an unsatisfiable circuit. This decides positive circuit solvability, contradicting its stipulated source/classical undecidability input.

This calculation preserves the fixed base Q and the full intermediate-field lattice; it is not a partial-field embedding argument. But all of its integration is already supplied by the literal symmetric top, classical symmetric inverse Galois construction, Galois correspondence, and the source's exact bounded-witness proof. There is no additional arithmetic coherence operation left by this check. It is not nominated.

The source stock S is fixed independently of the circuit values and the number of comparisons. Φ depends only on the unit count. B is derived from the hypothesized decision algorithm and is not asserted to have an explicit formula, efficient complexity, or a discriminant bound. The numerical value of N in S_N can depend on a circuit solution; this causes no circularity because it is |F|, not N, that is bounded before oracle queries.

### Existing work and unclaimed strengthening

Structural r18's actual `candidate.md` distinguishes the source's solution-dependent choice among finitely many tables from a total many-one map C↦L_C. That distinction still applies here. The argument above is an oracle/bounded-witness contradiction, not a one-output many-one construction or a claim of many-one completeness. We did not promote the same unresolved synthesis under a field-theoretic name.

Pálfy–Pudlák, [*Congruence lattices of finite algebras and intervals in subgroup lattices of finite groups* (1980)](https://math.hawaii.edu/~ralph/Classes/619/PalfyPudlak.pdf), Theorem 2 and its proof, assert an equivalence of two **universal** representation statements. Their proof first embeds a lattice in a larger lattice satisfying special properties; it is not a pointwise equivalence for an arbitrary fixed lattice. The arithmetic reduction above does not need that invalid inference. The source's actual weighted template and reading are used directly.

## 3. Integral/modular Chow normalization and polarization (210)

### Strongest source companion and history

The quadratic stabilization source `thm:main` treats complex vector spaces and gives the stated quadratic range for the canonical Foulkes–Howe map. Its `lem:shift` uses Fischer adjoints and a positive weight difference; the proof subsequently moves degree from one row to another. The sixth-power companion has a stronger whole-power polarization lemma (`lem:polarization`), an explicit multisymmetric affine chart (`lem:chart`), and a low-degree module-generation corollary (`cor:module-generation`). These operations were read, not inferred from the sixth-case headline.

Actual iterations I198, I199 and I202 already use this companion to sharpen the stable range and investigate the seventh seed through the deficiency module C=R/A. In particular their outstanding finite annihilation relation is not freshly rediscovered here. I202 also isolates the elementary-length issue in multisymmetric straightening. Parameter-only strengthening via the companion would not constitute a fresh mechanism.

The new feasibility direction examined whether an integral/divided-power formulation can preserve the normalization/polarization mechanism uniformly in characteristic. It was checked against two primary proof bodies before any freeze:

* Raicu–Sam–Weyman, [*On some modules supported in the Chow variety*, arXiv:2108.10910v1, retained NSF copy](https://par.nsf.gov/servlets/purl/10334188), Proposition 2.7 and Theorem 2.3: finiteness and normalization of the invariant ring, including the Vandermonde argument that does not divide by characteristic. Remark 2.9 distinguishes the projective-normality behavior in positive characteristic.
* Rydh, [*A minimal set of generators for the ring of multisymmetric functions*, Ann. Inst. Fourier 57 (2007), 1741–1769](https://www.numdam.org/article/AIF_2007__57_6_1741_0.pdf), Proposition 7.18, Theorem 7.19, Lemma 7.20, Corollaries 8.4 and 8.10 with their proofs. In particular the elementary generators suffice when d! is invertible. Corollary 8.10 gives a sharper exact classification, including its small-rank exceptions. One cannot simply label all positive characteristic behavior obstructed.

### A finite calculation and its existing primary identification

Take two rows (x_i,y_i,z_i), i=1,2, over F_2, with simultaneous row swap. In multidegree (1,1,1), write the four orbit sums as

\[
\begin{aligned}
t&=x_1y_1z_1+x_2y_2z_2,\\
u&=x_1y_1z_2+x_2y_2z_1,\\
v&=x_1y_2z_1+x_2y_1z_2,\\
w&=x_2y_1z_1+x_1y_2z_2.
\end{aligned}
\]

Products of elementary multisymmetric generators in that degree are spanned by

\[
 t+u+v+w,\qquad v+w,\qquad u+w,\qquad u+v.
\]

This list is exhaustive: generators have total degree one or two, and the multidegree has no repeated variable. To obtain coefficient 1 on t, the first generator must occur with coefficient 1. The remaining mixed vector (1,1,1) has odd parity, whereas the last three vectors span the even-parity subspace. Thus t is absent from the elementary-generated algebra. This is precisely the known characteristic-two obstruction represented by the three-variable generator in Rydh's Corollary 8.10 proof. It is not a new method obstruction or a nomination.

The projective persistence can be seen without numerical experiments. Homogenize the two rows with u_10,u_20 and let z_0=u_10u_20. In the row-bidegree (3,3) invariant ring put

\[
 F=u_{11}u_{12}u_{13}u_{20}^{3}
   +u_{21}u_{22}u_{23}u_{10}^{3}.
\]

On the chart z_0≠0, F/z_0^3=t. Let A be the homogeneous algebra generated by the coefficients of the product of the two linear forms, and R the row-swap invariant diagonal algebra. If z_0^kF belonged to A_{k+3}, division by z_0^{k+3} would put t in the elementary chart algebra. It does not. Hence this known modular defect survives in every degree b≥3. This concerns the invariant/divided-power normalization map in characteristic two; it must not be passed off as the characteristic-zero source map defined by averaging symmetric tensors. Ordinary symmetrization and divided powers cannot be interchanged in this characteristic.

The source differential mechanism has its own elementary characteristic warning: D_(Y←U)(U_1^p)=0 in characteristic p. That observation alone says nothing about whether an alternative tame-characteristic theorem holds. Rydh already supplies the strongest compatible elementary-generation statement in the tame regime p>a. What was not supplied by this screen is integral, degree-effective filtered control replacing all the source's weight-string/factorial and semisimplicity operations with the same quantitative range. Localized chart generation does not itself provide that bound. We froze neither a broad modular stabilization claim nor a parameter-restricted workaround. The finite calculation is explanatory evidence about an existing primary mechanism, not a mathematical gate.

## 4. Other exclusions and the stopping boundary

For 057, the pinned half-weight-divisor manuscript's transfer proof already works through general compact connected fibers with trivial cotangent and the specified divisorial/root pullback geometry. The actual OA057 public proof-comparison and review documents exhibit the earlier arbitrary finite SNC-root construction: permutation plus coboundary pairs descend root lines before resolution and preserve the needed proper divisorial sections. The two-step-monodromy companion's `linear.tex` uses the special quasi-Albanese reduction and its linear nilpotent structure; `ordinary.tex` expressly leaves the faithful-linear-representation interface unprovided. We did not infer virtual nilpotence of the entire fundamental group from linear images, or nominate another root-index variant. The primary bodies cited by OA057 were not all newly read; this is a historical proof-operation exclusion with that limit.

For 202, arithmetic r25's actual screen and parts of I108's actual derivation already address Galois weight equivariance and the twisted-tuple/index interface. Source files acquired during selection were removed unread, and no fresh operative research claim is made for this family. Its historical rating was not used as an independent mathematical verdict.

The actual r77 research and reading-limit records were consulted before related selection. Its finite tensor-category, cubic-point and central-gerbe investigations are not counted as r78 work. No excluded family from the assignment was reopened. Broad and focused content searches covered authored campaign/iteration/experiment bodies, construction strings and aliases without a size cutoff; the exact search limits and truncated displays are recorded separately. Negative search results are not worldwide priority clearance.

The strongest compatible reductions found here either close the screened implication by supplied operations (ordinary étale stability descent and fixed-Q whole-field-lattice recognition) or leave a precisely identified interface without a full proof (nonfree full numerical support and a uniform integral quantitative polarization replacement). The characteristic-two calculation is already accounted for in a primary proof. There is no eligible full candidate to send forward, no candidate freeze, and no weaker surrogate or method-counterexample nomination. Further independent review can assess this archive; this author assigns no contribution grade or campaign gate.
