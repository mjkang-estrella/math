# I75 — Polynomial twists: forced classes, missing higher pairings, and a Gaussian route

**Outcome: GAP; no substantial finding nominated.** C73-D and C73-M remain unproved and unrefuted. This round establishes a concrete obstruction to an unmodified all-integer Selmer argument on the actual curve `E:y²=x³−x`, pays the cost of *relaxing* the new odd local conditions, and develops a distinct Gaussian norm/transfer construction. It also gives exact arithmetic tests on actual twists and a proved sparse family of nonminimal analytic ranks. These are scoped technical partials, not a density theorem. Eight accepted findings remain eight; review, counting and publication belong to the parent.

All pinned OpenAI statements **and lower proof operations** are true premises. Their applicability is audited; their truth is not. External literature is not stipulated. Original arguments, new constructions and gaps are separated below. No I73 file, shared ledger, parent wrapper or other child's file was edited. No staging, commit, publication or delegation occurred.

The complete incoming message is frozen in [complete-message.txt](../sources/i75_polynomial_twist_selmer/complete-message.txt), including the role sentence, the I75 instructions, the complete I73 assignment and returned report. [brief.txt](../sources/i75_polynomial_twist_selmer/brief.txt) is the exact `brief` field of the parent's launch record. The I73 report, all its evidence/experiments, and `frontier/experiments/i73-parent-verification.json` are hash-referenced, not copied recursively, in [prior-references.json](../sources/i75_polynomial_twist_selmer/prior-references.json). Only `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md` have the informational-drift exception.

## 1. Exact target and independent original-argument audit

Fix an elliptic curve `E/Q`, its conductor `N`, and a positive `M` divisible by `8N`. Throughout,

\[
 d_n=M^2n^2+1,\quad \mathcal S_M(X)=\{1\le n\le X:d_n\text{ squarefree}\},
 \qquad b_E=(1-w(E))/2.
\]

C73-D asserts `#{n∈S_M(X):a(E^{d_n})>b_E}=o(X)`. C73-M asserts `Σ_{n∈S_M(X)}(a(E^{d_n})−b_E)=o(X)`. Analytic rank means order at the classical center `s=1`. All parameters `E,M` are fixed before taking limits. A finite rank calculation or a density-zero infinite exceptional family cannot refute either assertion.

The following is an independent audit of the **original I73 deductions actually used**, not approval of its open targets or an acceptance review.

* **ORIGINAL PASS — squarefreeness and fixed conditioning.** For odd `p∤M`, the number of roots of `M²u²+1` modulo `p` is `z_p=1+(−1/p)`; its roots are simple because `2M²u` is nonzero there. Each lifts uniquely modulo `p²`. At `p|2M` there are no roots. The stipulated squarefree-values paper's separable-product corollary and its actual fixed-cutoff sieve apply to this fixed primitive irreducible quadratic. Thus `|S_M(X)|=c_M X+o(X)`, where `c_M=∏_{p∤2M}(1−z_p/p²)>0`. For a bounded fixed local test, the difference between the finite presieve and true squarefreeness has limiting mass `c_z−c_M`; first take `X→∞`, then `z→∞`. This proves the claimed fixed-prime independence under squarefree conditioning. It gives neither a growing-modulus assertion nor permission to weight the discarded set by a growing Dirichlet polynomial.
* **ORIGINAL PASS — local character law, with its stated case distinction.** The bijection `(v−Mu)(v+Mu)=1` gives `Σ_u(d_u/p)=−1` for `p∤M`. Modulo `p²`, after excluding roots modulo `p²`, the numbers with character `0,+1,−1` are respectively `z_p(p−1), p(p−z_p−1)/2, p(p−z_p+1)/2`. Divide by `p²−z_p`. If `p|M`, the character is deterministically `1`. In particular the `p=3` mean is `−1/3` only if `3∤M`; it is `1` otherwise. I73 stated the distinction before its final shorthand example; no universal negative `p=3` mean is imported. **REPAIR: none to the mathematical law.** We spell out the qualification whenever that example is used.
* **ORIGINAL PASS — generic rank zero.** The double cover `v²=M²t²+1` has parameter `t=(u−u⁻¹)/(2M), v=(u+u⁻¹)/2`. A point of constant `E/Q(u)` extends to a morphism `P¹→E`; properness and Riemann–Hurwitz make it constant. The deck involution is `u↦−1/u`; an anti-invariant constant point is 2-torsion. This proves generic rank zero, also over algebraically closed constants. It says nothing about a sparse specialization subfamily; §7 supplies one with non-torsion points.
* **ORIGINAL PASS — finite levels and the one-sided limit argument.** For `A_n=Sel_{2∞}(E^{d_n}/Q)`, define `r_k(n)` by embeddings of `(Z/2^k)^r` in **this full group**, as in Smith's Notation 1.8. A cofinitely generated group is `(Q₂/Z₂)^s⊕⊕_i Z/2^{e_i}`, hence `r_k=s+#{i:e_i≥k}`. The inclusion `{s>b_E}⊂{r_k>b_E}` for every fixed `k` proves I73's sufficient iterated-limit criterion. Pointwise decrease in `k` does not interchange the limits. The finite Selmer group `Sel_{2^k}` has a torsion correction and is not this invariant by definition.
* **ORIGINAL PASS — analytic/algebraic separation.** `d_n` is a positive fundamental discriminant, a local square at every place dividing `2N`, and `w(E^{d_n})=w(E)`. The stipulated parity, full-corank converse and forward low-analytic-rank implication are applicable without extra CM, torsion, ordinary or good-reduction hypotheses. Low corank gives low analytic rank; an algebraic-rank moment by itself controls neither divisible Sha nor exceptional analytic ranks. The logarithmic individual Jensen bound leaves an `o(X/log X)` exceptional-count requirement for a direct mean transfer. The alternative uniform-integrability argument in I73 is ordinary truncation and is correct.

**GAP, unchanged:** none of those original arguments proves thin-family low-corank density, analytic uniform integrability, S73 or H73. The original restricted Gram comparison is also correct as used: a period `rad(ml)` and a bounded remainder give `2X⁻¹(Σm|a_m|)²`. Its short range is not a source-length analytic comparison. No new I75 deduction below is retroactively labelled an I73 ORIGINAL PASS.

## 2. Source operations actually inspected

[Passages.json](../sources/i75_polynomial_twist_selmer/passages.json) binds exact retained text ranges or rendered PDF pages. Full PDFs and capture metadata are retained for the new external sources. I73's full retained companions and its complete 9,340-file corpus/1,033-other-blob inventory are reused by hash and independently replayed. This was a focused continuation, not a repeated generic catalogue screen.

**Pinned sources.** Goldfeld October 7 `01-preliminaries` gives parity, finite-descent corrections and rationalization of isogeny/base-change maps. `09-local-matrices`, especially `lem:lm:arithmetic-realization`, realizes finitely prescribed prime templates by ray classes and Chebotarev, with reciprocity fixing reverse bits. `07-prime-graphs` constructs contraction/address programs from those realization freedoms; `08-rational-converse` pays full-two-torsion packets, reserve labels and common composita. These are accepted operations. None says that the product of the chosen primes is `M²n²+1`, or bounds the number of such products. The source explicitly allows the sizes of realizing primes to depend on the whole finite configuration. Its `11-conclusions` obtains distribution from Smith's all-integer theorem, not by counting the constructed packets. The mean-rank paper's comparison, Jensen and terminal-tail operations retain the budgets in §8. The squarefree paper's fixed-cutoff and separable-product operations also apply to the quartic in §7.

**Koymans–Smith, [2606.31649v1](https://arxiv.org/pdf/2606.31649v1).** The current official record still shows v1. Definition 2.6 requires an effectively equidistributed family of a *fixed finite Galois module*, with explicit local probabilities and a small-product range. Theorem 2.7 bounds normalized Selmer moments. Its quasi-decoration inequality (2.3) relaxes some local conditions while changing the Tamagawa bound in the opposite direction. Definition 4.2 and Proposition 4.3 transfer bounds on weighted product grids. Lemma 5.15, equations (5.25)–(5.26), rewrites the test pairing as a sum of double-coset residue symbols; reciprocity combines opposite directions and introduces only fixed-type constants. This is an actual bilinear character mechanism, not independence postulated for a matrix. It is used for upper moments after the sieve has left some primes uncontrolled. Example 7.9 chooses a member of a finite isogeny class minimizing a Tamagawa majorant; the chosen member can vary with the parameter. Higher torsion of quadratic twists is generally not a fixed Galois module: the sign twist becomes nontrivial on `E[4]`. The fixed-module theorem cannot simply be reapplied to `E[2^k]` for growing `k`.

**Koymans–Pagano–Sofos, [2409.02080v1](https://arxiv.org/pdf/2409.02080v1).** The full-two-torsion local planes in §2.4 are explicitly listed; their orthogonality gives Hilbert-symbol equations. Theorem 2.7 bounds a full matrix kernel by a cofactor-dependent principal minor times `4^{ω(cofactor)}`. The cofactor changes the diagonal; it is not discarded entirely. The proof of Theorem 1.1 in §5.2 actually bounds `Σ|Sel₂(E^{P(n)})|^j`, for each fixed integer `j`, before bounding rank. Its sieve and weighted Rédei calculation pay the remaining primes for this upper bound. Thus for the explicit full-two-torsion class below we can use an exponential tail for `r_1`, rather than only for Mordell–Weil rank. This stronger *source operation* is attributed, not nominated.

**Smith, [2503.17619v1](https://arxiv.org/pdf/2503.17619v1), and predecessors [I v2](https://arxiv.org/pdf/2207.05674v2), [II v2](https://arxiv.org/pdf/2207.05143v2).** The current main-paper record still shows v1. I's Definition 4.19 requires enough prefix and active indices and specific nonzero ramification pairings for every test plane. Its Theorem 6.2 controls Cassels–Tate characters on higher grid classes, and its Fourier step pays the number of possible pairings. II's Notation 8.4 imposes prime-type balance, small-prime bounds and preparation for higher work; its discarded-ideal estimate is in the full ideal/twist measure. The 2025 Theorem 2.4 permits more general **controllable tensors**, but still requires nonzero images under selected ramification projections and an actual higher grid class. It bounds a sum over that class by `(log log H)^(-1/4)` times the *base-class size*, with level/rank constraints. It is not a relative-error estimate for every sparse subset of the class. The §§2.5 and 6 operations use governing expansions, strict signatures and closed subsets of product grids. The polynomial slice is not shown to retain that closure or density.

**Other primary operations.** Zhang's [2025 paper, §§2.1–2.2](https://zhangshenxing.github.io/publications/Zhang2025.pdf) gives the precise Monsky coordinates, the 2-cover equations, and the tangent-plane Hilbert-symbol Cassels pairing; Lemma 4.1 identifies its kernel with the image of 4-Selmer after torsion. We use those classical descent facts, not its class-group criteria without their hypotheses. Morgan–Smith's [field-change paper](https://arxiv.org/pdf/2206.13403v1), Theorem 4.5, Example 4.6 and Corollary 4.9, transports the *decorated* module by local Shapiro maps and proves restriction/corestriction adjointness. The multiplication by the extension degree in (4.9)(3) is essential in §6. Dokchitser–Dokchitser [v4](https://arxiv.org/pdf/1208.5519v4), Lemma A.3, identifies the scalar quadratic inertia action used in §4. Tunnell's [original 1983 paper](https://sites.math.rutgers.edu/~zeilberg/EM22/JT1983.pdf), printed pp.327–329, supplies the exact theta coefficient and positive central-value formula used in §7; its scan was inspected visually, since the text extractor returns only the catalogue cover. None of these external mathematical results is promoted to a stipulated premise.

## 3. Approach A: an actual full-two-torsion descent

### 3.1 Forced splitting and a complete local class

Take `E₀:y²=x³−x`, of conductor 32; admissible `M` are divisible by 256. Write `E_d:y²=x³−d²x`. If `p|d=M²n²+1`, then `p∤2M`, and `(Mn)²≡−1 mod p`, so **every prime divisor is `1 mod 4`**. This is deterministic, not a finite-prime approximation. Distinct divisors therefore satisfy `(p/q)=(q/p)`. The number of prime factors `5 mod 8` is even because `d≡1 mod8`. Neither fact says all those symbols are `+1`; for `d=262145`, `(13/5)=−1`.

Here is a useful class whose local conditions can be paid without a statistical model. Use Kummer triples `(x−d,x+d,x)` and the associated cover

\[
 H_1:-dt^2+d_2u_2^2-d_3u_3^2=0,\quad
 H_2:-dt^2+d_3u_3^2-d_1u_1^2=0,\quad
 H_3:2dt^2+d_1u_1^2-d_2u_2^2=0.                 \tag{1}
\]

Set `τ_d=(d,d,1)`. At every `p|d`, choose `i_p²=−1` in `Q_p`; `(t,u₁,u₂,u₃)=(1,i_p,1,0)` solves all three equations. At 2, `d≡1 mod8` is a square, and `(0,1,1,√d)` is a point. The same point works at infinity. At each remaining odd prime, `E_d` has good reduction and the triple consists of units, hence defines an unramified class; the local Kummer image at a good odd prime equals the unramified subgroup. This last equality follows from the étale multiplication-by-2 map on the good integral model and the finite-field Kummer sequence (Lang's theorem). Thus no local place is omitted.

The torsion triples are

\[
 (1,1,1),\ (2,2d,d),\ (-2d,2,-d),\ (-d,d,-1).
\]

For positive squarefree `d>1`, `τ_d` is none of them modulo coordinatewise squares: the third coordinate eliminates the last three, and `d` eliminates the identity. Also no nonzero rational 2-torsion point is divisible by 2 over `Q`: at the roots `0,d,−d`, the differences to the other roots are respectively `±d`, `d,2d`, and `−d,−2d`; the standard halving criterion would require both differences to be squares. Thus the torsion quotient here agrees with Smith's `r_1`.

Consequently `r_1(E_d)≥1`. In fact `r_1(E_d)≥2`: the Monsky computation below proves it directly. Alternatively the stipulated finite-descent parity says `r_1≡s≡0 mod2` because `w(E_d)=w(E₀)=+1`. This is a **deterministic finite-Selmer obstruction**. It is not a Mordell–Weil, full-corank or analytic-rank obstruction.

### 3.2 The exact matrix and the invisible ramification direction

Let `d=p₁⋯p_t`. Over `F₂`, put `A_ij=[p_j/p_i]` off the diagonal, `A_ii=Σ_{j≠i}A_ij`, and `D=diag([2/p_i])`; brackets are additive Legendre symbols. The complete Monsky descent, including the 2-adic and real conditions, identifies the pure 2-Selmer group with

\[
 \ker\begin{pmatrix}A+D&D\\D&A+D\end{pmatrix},
 \qquad (d_1,d_2,d_3)\mapsto(\psi(d_2),\psi(d_1)).          \tag{2}
\]

This is the classical theorem in Zhang (2.4)–(2.5), not a new matrix surrogate for an elliptic curve. Its hypotheses here are exactly odd, positive, squarefree `d`; our primes `1 mod4` make `A` symmetric and `D_{−2}=D_2`. The support reduction to positive divisors of `d` uses the torsion triples and the conditions at 2 and infinity; simply dropping those conditions would give a different group. The independent local construction in (1) also checks the particular class needed below.

Let `K=ker A`, `h=dim K`. With `u=x+y`, the equations become `Au=0`, `Ax=Du`. Since `A` is symmetric, `im A=K^⊥`; hence

\[
 r_1(E_d)=h+\dim\{u\in K:Du\in K^\perp\}
          =2h-\operatorname{rank}(D|_{K\times K}).        \tag{3}
\]

Always `1∈K`. If `h≥2`, the subspace `(x,x)` already gives dimension at least two. If `h=1`, then `1ᵀD1=0`, since there are evenly many primes `5 mod8`, so `D1∈im A`; (3) gives dimension two. This proves the asserted lower bound for every admissible value.

There is a sharper applicability issue for the higher-pairing source. Multiply `τ_d` by the torsion triple `(-d,d,-1)`. Its pure class is represented by

\[
 \eta=(-1,1,-1).                                         \tag{4}
\]

This cohomology class is independent of `n` in the constant module `E₀[2]` and is **unramified at every odd prime**. At every new twist prime, the ramification projections `π_p` of (4) are zero. The torsion ramification map at such a prime is an isomorphism onto the two valuation coordinates, so a prefix complement retains this nonzero pure class as its unramified representative. Since `r_1≥2`, choose a second independent pure class `v`. For `w=η∧v`, every two-prime tensor test in Smith's Definition 2.3 has zero image: each term contains a factor `π_p(η)=0`. In particular the all-test-plane readiness condition in predecessor I, Definition 4.19(5), fails for this plane. The 2025 controllable-tensor theorem makes no assertion about this `w`.

This is a concrete missing arithmetic direction **even before discarding the largest prime entries**. It does not prove that the true Cassels pairing of `η` with `v` is zero, nor that `η` survives to level 2. Those require the actual tangent forms or a governing expansion with its fixed-place contributions. The residue-matrix rank alone does not evaluate them. The relevant first pairing is

\[
 \langle\Lambda,\Lambda'\rangle
  =\sum_v\sum_{i=1}^3 [L_i(P_v),d'_i]_v,                \tag{5}
\]

where each `L_i` is tangent to the corresponding rational conic `H_i=0` and `P_v` lies on the full cover. Replacing (5) by independent Legendre bits at the new primes would remove precisely the direction (4). Even restricting to `h=1` does not pay that step. No claim about a universal 4-Selmer obstruction is made.

### 3.3 Torsion, isogeny and CM cases are different

For `E₀`, the quotient by `(0,0)` is `y²=x³+4x`, with 2-torsion field `Q(i)`, while the other two 2-isogenous quotients have 2-torsion field `Q(√2)` (translate a root first: `A=±3,B=2`, and the quotient discriminant is `16B=32`). Thus **none** of its three rational 2-isogenies is balanced in Smith's definition. It has full rational 2-torsion and CM, but this places it in Case I, not a balanced case. All new primes split in the `Q(i)` quotient field; the full-integer prime-type law is genuinely changed.

For a concrete non-CM balanced example use `F:y²=x(x+1)(x+4)`. Its quotient at `(0,0)` is `y²=x³−10x²+9x=x(x−1)(x−9)`. Both 2-torsion fields are `Q`. The quotients at the other roots have nonsquare `B=−3,12`, so this is the unique balanced isogeny (Case IV). The invariant `j=35152/9` is nonintegral, hence this curve is not CM. The only possible bad primes are 2 and 3. For `8N_F|M`, `d_n` is a square at both and positive at infinity, so these local twist conditions are the original ones. At every new prime the two full-two-torsion curves have the same local 2-torsion size; Smith's balanced local Euler-characteristic calculation gives local Tamagawa-ratio contribution one. The fixed ratio does **not** give distribution of its isogeny Selmer group on the polynomial slice. The prime-pair constraints and higher pairing remain to be counted. No result for this example is inferred from the CM example.

For a general `E`, KS's finite isogeny minimum can be used for a moment bound on a selected member. If the maps in a fixed finite class have 2-primary degree at most `2^e`, maps and duals respecting Kummer conditions give

\[
 r_{k+e}(E^d)\le r_k(B^d),\qquad r_{k+e}(B^d)\le r_k(E^d).
                                                               \tag{6}
\]

Indeed an isogeny's kernel on full Selmer is killed by its degree; its image of a free `(Z/2^{k+e})^r` subgroup contains `(Z/2^k)^r`. The corank is unchanged, but the finite levels need the shift. A selector depending on `n` must be included in the statistical conditioning or paid by summing errors over the fixed finite class. It cannot silently become an independently sampled curve.

## 4. A paid missing-row lemma, and its precise limitation

**Technical lemma.** For any fixed `E/Q`, any admissible squarefree `d=M²n²+1`, and any subset `T` of primes dividing `d`, let `A` be the full `2∞`-Selmer group with all Kummer conditions. Let `A^rel` impose the same conditions except that the local condition at each `p∈T` is unrestricted. Then

\[
 2A^{\rm rel}\subset A\subset A^{\rm rel},\quad
 \#(A^{\rm rel}/A)\le4^{|T|},\quad
 r_{k+1}(A^{\rm rel})\le r_k(A)\le r_k(A^{\rm rel}),
 \quad\operatorname{corank}A^{\rm rel}=\operatorname{corank}A.
                                                               \tag{7}
\]

**Proof, including the local exponent.** Every `p∈T` is at least 5 and is a good-reduction prime of `E`. On `E^d[2∞]`, a ramified quadratic inertia element acts as `−1`, since the original Tate module is unramified. Thus all `Q_p`-rational 2-primary torsion is killed by 2 and has size at most four. The compact group `E^d(Q_p)` has an open pro-`p` subgroup; multiplication by 2 is invertible on it. Its finite 2-primary quotient splits off and identifies with the rational 2-primary torsion. Consequently its 2-adic completion has exponent at most 2 and order at most four. Local Tate duality identifies `H¹(Q_p,E^d)[2∞]` with its dual, so it too has exponent at most 2 and order at most four. The Kummer exact sequence identifies this with the quotient of local cohomology by the full Kummer image. Localization therefore embeds `A^rel/A` in their product over `T`, proving the first two claims. Multiplying an embedded `(Z/2^{k+1})^r` in `A^rel` by 2 gives an embedded `(Z/2^k)^r` in `A`; inclusion gives the other inequality. The quotient is finite, proving equality of coranks. This proof retains the conditions at 2, all old bad primes and infinity throughout. ∎

The one-level shift is independent of `|T|`; the *cardinality* bound is not. For a threshold `X^θ`, at most `2/θ+o(1)` prime factors of a value with `n≤X` exceed it, because their product is at most `M²X²+1`. This count is bounded, not `o(1)` and not a negligible exceptional set.

Equation (7) genuinely pays the cost of missing **rows in full cohomology**. It does not justify the KPS principal-minor replacement: that replacement also removes ramification **coordinates/columns** and retains cofactor-dependent diagonals, with the displayed `4^{ω(cofactor)}` loss. More importantly, the relaxed local condition is no longer self-dual. Its dual condition is strict zero at the omitted places; its Cassels–Tate pairing is between differently decorated objects, not the alternating self-pairing of the original full group. Thus applying Smith's alternating transition probabilities directly to `A^rel` is invalid. The missing work is to construct and count the appropriate strict/relaxed higher tests (and the fixed-support direction (4)), not to add an arbitrary exponentially small error for the last primes.

## 5. An attempted quantitative survival construction

For the explicit full-two-torsion class, KPS's actual proof gives, for every fixed `λ>0`,

\[
 \limsup_{X\to\infty}|\mathcal S_M(X)|^{-1}
      \sum_{n\in\mathcal S_M(X)}e^{\lambda r_1(n)}
 \le C_{E,M,\lambda}/c_M<\infty.                       \tag{8}
\]

Take an integer moment large enough that `2^j≥e^λ`, use `2^{r_1}≤#Sel₂`, restrict the nonnegative sum, and divide by the squarefree density. Thus the discarded event `r_1>R` costs at most `(C/c_M)e^{−λR}`. For other curves only the selected-isogeny version discussed above is available from the inspected KS operation.

Here is a specified sufficient estimate which would complete the *arithmetic* density argument for `E₀`. It is stronger and more structured than the bare SC73 limit. On the squarefree probability space, after fixing all previous higher pairings and their Kummer/torsion identifications, let `V_j=2^{j−1}A[2^j]`. Its alternating level-`j` pairing has radical `V_{j+1}`. Work on `r_1≤R`. Partition the genuine polynomial sample into decorated histories `h`, including orientations, cofactor information and any isogeny selector. Let `ε_j(X,R)` be the **mass-weighted total variation error**, summed over those histories, between the actual next-pairing law and the uniform law on alternating forms on `V_j`. Add `δ_j(X,R)` for the mass whose coordinates or tests have not been constructed. This definition uses actual elliptic pairings, not a replacement random family.

If these tests existed with `ε_j+δ_j→0` for every fixed `R,j`, then

\[
 \Pr_{\mathcal S_M(X)}(r_k>0)
 \le (C/c_M)e^{-\lambda R}+(7/12)^{k-1}
       +\sum_{j<k}(\epsilon_j(X,R)+\delta_j(X,R))+o(1).
                                                               \tag{9}
\]

**Proof of the conditional bound.** The corank and every `r_j` have even parity here: the finite Cassels–Tate summands occur in equal-order pairs and the corank has sign `+1`. A uniform alternating form on an even `r`-space is nondegenerate with probability `∏_{i=1}^{r/2}(1−2^{1−2i})`. This is obtained by counting symplectic bases, or choosing successive hyperbolic pairs. The product is at least `(1/2)(1−Σ_{i≥2}2^{1−2i})=5/12`. Thus a positive state survives one step with probability at most `7/12`; zero is absorbing. Conditioning on histories, total variation bounds the change in this event's probability; sum the actual history masses and the discarded mass, then induct. The initial tail is (8). Take `X→∞` at fixed `R,k`, then `k→∞`, then `R→∞`. Equation (9), if its arithmetic estimates were proved, would imply C73-D through the stipulated converse. No bounded-moment argument alone supplies its decreasing geometric term. ∎

For comparison with Smith's *actual Fourier operation*, on a history of dimension `r≤R`, there are `Q_r=2^{r(r−1)/2}` possible pairings. If every nontrivial character has unnormalized sum bounded by `B_h`, Fourier inversion gives an `L¹` error at most `Q_r B_h`; after normalization and summing histories, a sufficient budget is

\[
 {2^{R(R-1)/2}\over |\mathcal S_M(X)|}
          \sum_h B_h=o_{R,j}(1).                       \tag{10}
\]

Small history masses are handled by this weighted sum, not by dividing an ambient bound by an arbitrarily tiny history. Smith's error is proportional to an ambient base-grid class of height comparable to `X²`; even one such ambient bound need not be `o(X)`. Neither KS's positive moment majorant nor an absolute Chebotarev realization bound gives (10). The direction `η∧v` is not controllable by the inspected ramification tests. A strict/relaxed version must also pay the dual local-condition change in §4. **These are the concrete gaps in (9), not asserted estimates.** In particular there is no proved survival contraction at any unbounded sequence of levels in this polynomial family.

Squarefree conditioning costs exactly `c_M` for bounded events and fixed tests. It does not supply (10) for growing families of histories. The rank cutoff `R`, the level `k`, the support threshold and any isogeny shift must remain fixed during the `X` limit; no dependence of the source's constants on those quantities has been suppressed. For general sign `b_E=1`, a different transition bound on odd-dimensional spaces would be needed; (9) has only been formulated and proved conditionally for the sign-even explicit class.

## 6. Approach B: Gaussian norms with the full Kummer conditions

### 6.1 Oriented factors form a thin line, not a product grid

Put `a=Mn`. In `Z[i]`,

\[
 d=(1-ai)(1+ai),\qquad \gcd(1-ai,1+ai)=1.
\]

A common Gaussian divisor would divide 2 and `1-ai`; the latter has odd norm, so the gcd is a unit. Each rational prime dividing squarefree `d` therefore contributes exactly one of its two conjugate Gaussian primes to `α=1-ai`. Since `4|a`, `α` is primary (`α≡1 mod(1+i)^3`). Choosing primary factors fixes their units and their product exactly, not merely its norm. Quadratic reciprocity of the rational primes was already forced in §3; further Gaussian residue symbols have to respect this orientation and this product equation. The identity also supplies the unit of norm `−1`, `a+√d`, in `Q(√d)`, but no elliptic rank conclusion follows from a negative Pell solution.

For a Gaussian divisor `β=u+vi` of `α`, write its cofactor `γ=r+si`. Then

\[
 ur-vs=1,\qquad us+vr=-Mn.                             \tag{11}
\]

Necessarily `gcd(u,v)=1`. If `(r₀,s₀)` solves the first equation, every solution is

\[
 r=r_0+v\ell,\quad s=s_0+u\ell,\quad
 us+vr=b_0+(u^2+v^2)\ell.                             \tag{12}
\]

Thus, for a fixed oriented divisor of norm `m`, the allowed inputs lie in one root progression modulo `m`, of length at most `X/m+1` in `[1,X]`; `gcd(M,m)=1`. This directly exhibits the thin cofactor constraint. Replacing a Gaussian prime factor independently will generally destroy `Re α=1`. Neither an ideal-box Selmer law over `Q(i)` nor the class number one of `Z[i]` counts the slice (11).

At a prime `p|m`, the residue of `d_n/m` depends on the lift of `n` modulo `p²`, not just on its root modulo `p`. A bounded test of all these residues is periodic modulo `m²`, with an elementary normalized discrepancy at most `2m²/X`. This pays one *specified fixed* oriented-divisor test; a range `m≤X^{1/2−ε}` makes that individual error small, but does not pay a sum over all divisors, governing fields or histories. It explains concretely why the cofactor-dependent diagonal in KPS is retained.

A possible new estimate would have to bound signed higher-pairing sums on (11), with `N(βγ)` in the required range, `Im(βγ)∈−M[1,X]`, the prior Selmer history fixed and squarefreeness imposed. For example the missing sum in (10) becomes a sum of absolute character discrepancies over these oriented factorizations, counted **once per chosen history**, not once per every divisor of `α`. A weighted upper sieve cannot yield this signed cancellation or its normalization for free. No such estimate is proved here.

### 6.2 The transfer exists; its pairing loss is essential

Let `K=Q(i)` and `A=E^d`, for an arbitrary rational `E`. Restriction and corestriction commute with every local Kummer map: restriction sends a local point to the same point over the extension, and corestriction sends Kummer classes to the Kummer class of the sum of conjugate points. This holds also above 2, at the old bad primes and at infinity. Their composite is multiplication by 2. Consequently

\[
 r_{k+1}\bigl(\mathrm{Sel}_{2^\infty}(A/\mathbf Q)\bigr)
 \le r_k\bigl(\mathrm{Sel}_{2^\infty}(A/K)\bigr).        \tag{13}
\]

To check the elementary-group step: on a subgroup `B≅(Z/2^{k+1})^r`, the kernel of restriction lies in `B[2]`. The quotient `B/(B∩ker res)` surjects onto `B/B[2]≅(Z/2^k)^r`; its invariant factors therefore contain a subgroup of the latter type. This proves (13), without treating an integral eigenspace decomposition as a direct sum.

Morgan–Smith's local Shapiro construction identifies the left-over number-field Selmer problem with the Selmer group of the Weil restriction, **with its transported local conditions**. It does not identify it with a rational elliptic curve. On Cassels–Tate pairings its adjointness gives

\[
 \langle\operatorname{res}x,\operatorname{res}y\rangle_K
     =2\langle x,y\rangle_{\mathbf Q}.                 \tag{14}
\]

For the first 2-valued pairing, the right side is zero. In particular testing only the pairings of restricted rational classes over `K` can never certify nondegeneracy of the rational first pairing. Cross-pairings with classes outside that image, or a higher-level lift carrying the lost factor of 2, are required. This is an exact arithmetic defect of that attempted transfer, not an abstract matrix objection.

For `E₀`, the `−1` twist is rationally the same curve, and the stipulated rationalization gives

\[
 s(E_d/K)=2s(E_d/\mathbf Q),\qquad
 L(E_d/K,s)=L(E_d/\mathbf Q,s)^2.                       \tag{15}
\]

The canonical class (4) becomes a squareclass-trivial cohomology class over `K`; equivalently `τ_d` becomes the Kummer class of rational 2-torsion. Thus a real first-level class is lost by restriction, exactly as (13) allows. Its disappearance proves neither that its rational Cassels pairing is nondegenerate nor that it lies in finite Sha rather than in the Mordell–Weil Kummer subgroup. New twist primes split in `K`, so their local fields and Kummer images are individually unchanged; the obstruction is not a hidden omission of one of those places.

A route proving `r_k(E_d/K)` small on the Gaussian line would, with the shift in (13), imply low rational corank. But no such number-field distribution is supplied by modularity over `K`; in the CM case (15) merely restates the desired rational corank at the infinite level. An arbitrary Bianchi curve has neither this rational decomposition nor a new converse from it. S73 is unchanged.

## 7. Arithmetic stress tests and a sparse rank-producing construction

### 7.1 An actual rank-zero twist with the forced Selmer class

For an odd positive squarefree `d`, let

\[
 A(d)=\#\{(x,y,z)\in\mathbf Z^3:2x^2+y^2+32z^2=d\},\quad
 B(d)=\#\{(x,y,z):2x^2+y^2+8z^2=d\}.
\]

Tunnell's coefficient is `a_T(d)=A(d)−B(d)/2`. The exact formula on printed pp.328–329 is

\[
 L(E_d,1)={\beta\over4\sqrt d}\,a_T(d)^2,\qquad
 \beta=\int_1^\infty {dx\over\sqrt{x^3-x}}>0.          \tag{16}
\]

The integral here is Tunnell's period convention; it is **not** silently substituted for the all-real-components Néron period in the stipulated BSD formula. We only use positivity and the exact formula (16).

At `M=256,n=1`, `d=65537` is prime. Exact enumeration gives `A=672`, `B=1280`, so `a_T=32` and `L(E_d,1)=256β/√65537>0`. Therefore analytic rank is zero. The stipulated forward implication gives Mordell–Weil rank zero, full corank zero and finite Sha. Meanwhile (2) is the zero 2-by-2 matrix, so `r_1=2`. This proves on an actual admissible curve that the forced finite Selmer obstruction can coexist with minimal analytic rank. No claim about the precise exponent or full order of Sha is needed.

The finite enumeration is certified in two different integer ways: direct bounded ternary enumeration, and Tunnell's signed binary-Hecke theta convolution from printed p.327,

\[
 a_T(d)=\sum_{(m,z,t)\in\mathbf Z^3\atop(4m+1)^2+8z^2+2t^2=d}(-1)^z.
\]

The proof of the finite analytic conclusion uses the external primary identity (16), not an approximate `L` evaluation. These finite checks are not evidence for an asymptotic frequency of rank zero.

### 7.2 A full proof of a sparse nonminimal-rank family

The generic rank-zero check does not preclude a quadratic subfamily in the input. For every integer `t≥1`, put `d=4t⁴+1`. On `E_d` there is the explicit point

\[
 P_t=(-4t^2,\ 2t(2-d)).                               \tag{17}
\]

Indeed `x³−d²x=4t²(d²−16t⁴)=4t²(d−2)²=y²`, using `d−1=4t⁴`.

It is non-torsion. Choose an odd prime `q|(d−2)`; this exists since `d−2=4t⁴−1≥3`. Then `q∤2td`, so the integral curve has good reduction at `q`. The duplication slope has numerator `3x²−d²≡8 mod q` and denominator `2y=4t(2−d)` divisible by `q`. Hence `x(2P_t)` has negative `q`-valuation: the slope-square term has negative valuation and the integral `−2x` cannot cancel it. The nonzero point `2P_t` lies in the formal group over `qZ_q`, which is torsion-free for odd `q` by its convergent formal logarithm. Thus `P_t` is non-torsion. This also gives a direct local certificate for every displayed point, rather than trusting a rank program.

For `M=256`, set `t=16u`, so `n=2u²` and

\[
 d_n=262144u^4+1=(512u^2-32u+1)(512u^2+32u+1).         \tag{18}
\]

The two quadratics are distinct, separable and have no common root; the value at zero is 1. The stipulated separable-product squarefree theorem therefore gives a positive constant `c_Q` with

\[
 \#\{n\le X:n=2u^2,\ d_n\text{ squarefree}\}
       =c_Q\sqrt{X/2}+o(\sqrt X).                     \tag{19}
\]

The point (17) gives positive Mordell–Weil rank on each such twist. If its analytic rank were zero, the stipulated forward theorem would force Mordell–Weil rank zero; hence its analytic rank is positive. Its root number is `+1`, so its analytic rank is at least two. In particular `n=2,d=262145=5·13·37·109` has point `(-1024,-8388576)`, and the exact Tunnell count independently gives `A=768,B=1536`, central value zero. Its pure 2-Selmer dimension is four; no exact algebraic rank or Sha finiteness is inferred from that upper bound.

For a general admissible fixed `M` for `E₀`, the less economical choice `t=Mu,n=2Mu²` gives the same construction and a positive `M`-dependent multiple of `√X` squarefree indices by the same theorem. This is an infinite sparse exceptional family, of density zero in the required `n` variable. It implies neither failure of C73-D nor failure of its `o(X)` mean. It also does not contradict generic rank zero: the substitution `n=2u²` changes the rational double cover to a genus-one quartic, which can map nontrivially to a constant elliptic curve.

**Contribution assessment:** (17) is a classical quartic/Jacobian-style congruent-number construction, and (19) is a direct application of the stipulated squarefree operation. It is not a new substantial finding. Its purpose is to test proposed deterministic conclusions on actual elliptic curves.

### 7.3 A concrete analytic nonvanishing route, still unpaid

In the CM test class C73-D is equivalent to the following anti-concentration problem for an exact signed lattice count:

\[
 C_M(n)=\sum_{2x^2+y^2+8z^2-(Mn)^2=1}(-1)^z
        =2A(d_n)-B(d_n),\qquad
 \#\{n\in\mathcal S_M(X):C_M(n)=0\}=o(X).              \tag{20}
\]

The equivalence is exactly (16); it does not assume BSD on the zero coefficients. This is a genuinely different prospective mechanism from higher Selmer survival: signed ternary representations on a quadratic slice. It is related to the Gaussian construction through Tunnell's Hecke character description, but the cancellation is global. A second or exponential moment bound does not prove the atom at zero tends to zero. Even a positive proportion of nonzero coefficients would not prove density one. The sparse zeros in (18) are actual zeros to be allowed, not discarded as impossible.

No estimate proving (20) is available in this round. In particular a Weil bound for a completed *short* polynomial-character sum does not give this theta-coefficient anti-concentration. Equations (11)–(14) identify what a relative descent/transfer must preserve, and (20) specifies an independent analytic target on the same explicit curve; none replaces an elliptic assertion by an abstract random-matrix theorem.

## 8. Analytic tails and all remaining general scope

No analytic comparison theorem has been transferred here. If that route is resumed, on `X<n≤2X` the twist size is `Y≈M²X²`. The inspected mean-rank source needs main length `Y^{1−Δ}`, with `Δ≤1/2`, hence length at least of order `X`; I73's elementary Gram comparison pays only `L<X^{1/3}`. The squarefree local character law is biased. A source-coefficient comparison must handle those specific coefficient norms and scaled derivatives, the growing multiplier, squarefree **weighted** large-square removal, the model Euler products, the terminal series and the source's independent minimal-rank input. None is supplied by (7), (8), a short completion estimate or (16).

For clarity the exact conditional mean budget remains: if `A_X={n∈S_M(X):s(n)>b_E}`, then the stipulated converse gives

\[
 \sum_{n\in\mathcal S_M(X)}(a(E^{d_n})-b_E)
   =\sum_{n\in A_X}(a(E^{d_n})-b_E).
\]

The individual analytic rank is `O_{E,M}(log X)`. Thus `|A_X|=o(X/log X)` suffices for C73-M. Merely `o(X)` suffices only for C73-D. Alternatively C73-D plus analytic uniform integrability suffices. A polynomial-sample tail `#{a>k}≪X/k²` up to `(log X)^{3/5}`, together with Jensen, would pay the terminal mass by `O(X/R)+O(X(log X)^{−1/5})`; no such tail is proved. The KS/KPS algebraic or finite-Selmer moments do not replace it.

The exact remaining scope is therefore broad: C73-D is not established even for the fixed curve `y²=x³−x` and `M=256`, let alone for the non-CM balanced example or all `E/Q`. No deterministic or positive-density analytic/corank counterexample has been found. The forced class (4), the verified rank-zero example and the sparse positive-rank construction explain why finite Selmer size, CM, norm representation and generic rank must be kept separate. S73, H73 and the other children's targets are untouched.

## 9. Evidence, corrections and replay

Run from the project root:

```bash
python -B frontier/experiments/i75_polynomial_twist_selmer/verify.py
```

The verifier is offline and read-only. It checks the immutable I75 seal and exact file domain, the full frozen brief against the parent brief, every I73 hash reference including its parent replay, the exactly-four-ledger exception, passage bindings, request/body hashes, capture-time version observations, new PDF text extraction and the retained scan renders through stdout. It invokes the unchanged I73 verifier, which rechecks the full 9,340-file corpus, 1,033-other-blob inventory, pin bindings, companions, earlier responses and finite diagnostics. It reruns the I75 exact diagnostics and compares their structured result. It never refreshes any seal.

The diagnostics check actual polynomial prime factors and Monsky matrices, the dimension identity (3), Gaussian primary orientations and (11), local points for (1), two independent integer calculations of the Tunnell coefficients, exact points and their formal-group non-torsion certificates, and finite algebra for the explicitly *conditional* transition and one-level-shift arguments. The 150-input matrix sample is finite and has no distributional interpretation. No diagnostic computes a universal Selmer tower or validates (9), (10) or (20).

A pre-seal diagnostic failed because the independently coded Hecke-theta convolution transcribed `(-1)^m` instead of the original paper's `(-1)^z`. Its initial bytes and failure description are retained; the corrected formula matches the separately implemented direct ternary counts. No original I73 proof was repaired. A passage-binder preflight also rejected a guessed terminal line 200 in a 198-line source; its initial builder and correction record are preserved, and final bindings record actual bounded ranges. Other provenance limitations are disclosed: early terminal reads were too broad and truncated, one guessed PF path was absent and was corrected by a no-ignore inventory, an oversized thread-read request failed before successful chunked recovery, and the Tunnell PDF text layer is catalogue-only. Search snippets were discovery leads, not proof inputs. Full relevant scan pages, not the text layer or a secondary summary, support (16).

This is version 1, sealed after the local checks. The seal and this version must be retained if a later correction is needed. **Replay PASS means provenance and exact finite reproduction only.** No independent original-proof acceptance, contribution approval, worldwide-priority claim, substantial nomination or count increment is asserted.
