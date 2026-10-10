# i05 — Joint Artin: the cubic obstruction and the exact remaining distribution problem

Date: 2026-10-08. Premise: every theorem in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is accepted as true, and R006 is available as the project's previously reviewed deduction. **Verdict: this investigation does not supply another substantial new theorem.** It supplies complete, but routine, strengthened index bounds; a precise obstruction to the progression-only proof; and a substantially narrower analytic target for further work. The sharp algebraic criterion requested in the brief is already in the primary literature. Its genuinely missing application here is a cubic-Frobenius-conditioned large-factor reservoir, not another algebraic compatibility criterion.

I read the project instructions, pin, complete preprint tree, relevant catalogue entries, iteration record, R004, R006, the arithmetic round-2 review, the full round-3 proof, and the round-4/5 reviews. The catalogue and **untruncated** `sources/preprints-tree.json` were searched for other applicable prime/Hecke/Frobenius results. The actual P, T and D statements below were downloaded from the immutable revision and checked against the tree, rather than inferred from the catalogue. No other agent was invoked. All writes are confined to this report and `frontier/{sources,experiments}/i05_joint_artin/`. No staging, commits, or shared-index changes were made.

## 1. Prior art checked before choosing the target, and again after the proofs

1. **Lenstra, On Artin's conjecture and Euclid's algorithm in global fields (1977), Theorems 3.1, 4.1 and 4.6.** The finite-level nonvanishing criterion is algebraic; the number-field prime-density conclusion assumes GRH. Crucially, this paper's subgroup-surjectivity problem is not identical to requiring each member of a list to be a primitive root. Its finite Frobenius restrictions already go beyond progressions. [Author's original paper](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1977d/art.pdf).
2. **Lenstra–Moree–Stevenhagen, Character sums for primitive root densities, Theorem 3.3, Corollary 3.4, Theorems 5.7–5.8 and §6.** These give the character-sum mechanism, progression obstructions, and near-primitive-root formulations. In particular, the exceptional cubic obstruction in progression problems is old. [Primary manuscript](https://archive.mpim-bonn.mpg.de/id/eprint/3969/1/preprint_2013_25.pdf).
3. **Moree–Stevenhagen, Computing higher rank primitive root densities, Theorems 5.6 and 6.2.** This is the decisive source for arbitrary dependent signed bases: the quadratic obstruction and the exceptional cubic hyperplane-covering obstruction are both explicitly classified. The text also gives the four-base obstruction used below. The density as a Haar measure is algebraic; its identification with the prime density is GRH conditional. [Version 2](https://arxiv.org/pdf/1203.4313v2).
4. **Anwar–Pappalardi, On simultaneous primitive roots (2017), main theorem, Proposition 1 and Lemma 1.** The same infinitude criterion is obtained under Schinzel's Hypothesis H. Lemma 1 already supplies the quadratic-reciprocity/CRT realization avoiding residue 1 at primes greater than 3. Thus that realization cannot be offered as a new difficult step here. [Publisher's paper](https://www.impan.pl/shop/publication/transaction/download/product/92279).
5. **Moree, On primes in arithmetic progression having a prescribed primitive root. II, Theorems 1–4.** The single-base progression density and its vanishing conditions are already known under GRH. [Version 1](https://arxiv.org/pdf/0707.3062v1).
6. **Järviniemi–Perucca, Unified treatment of Artin-type problems (2023), Main Theorem, Theorem 4.1, Remark 4.2 and Lemma 3.3.** Found in the closing search and read before finalizing the verdict. This already treats mixed index constraints with prescribed Frobenius and finite computational criteria under GRH. Its proof uses a GRH Chebotarev error through nearly the square-root range. The accepted width `10^-6` cannot simply replace that error. Thus repackaging a finite feasibility algorithm for mixed orders would not solve the requested novelty problem. [Primary publication](https://doi.org/10.1007/s40993-022-00418-6).

Initial searches included “Lenstra Moree Stevenhagen character sums primitive root densities multiple primitive roots positivity criterion -3”, “simultaneous primitive roots integers positivity criterion Schinzel multiplicative dependence entanglement”, and “Anwar Pappalardi simultaneous primitive roots Schinzel Hypothesis H 2017 criterion”. Later searches included “Poisson-Dirichlet Chebotarev”, “prime predecessors Frobenius”, and the four queries saved in `final-search.json`. Primary manuscripts, not search snippets, support the mathematical comparisons. No inference of worldwide priority is drawn from absent hits.

The accepted companion **T**, *Simultaneous primitive roots: a conditional lower bound for prime bases*, `sections/01-introduction.tex`, `thm:main`, is accepted here with its four companion inputs. It already proves `≫ x/log²x` for distinct positive prime bases. Its §2 makes the bases nonsquares in a class with `p≡5 mod8` and excludes other index primes. Upgrading that class argument using R006 is routine. None of the results below is counted as a separate substantial discovery.

## 2. Exact inputs used in the complete deductions

Write `N(x)=π(2x)−π(x)`, `δ=10^-6`, and `i_p(a)=(p−1)/ord_p(a)` when `p∤a`. All bases and moduli below are fixed before `x→∞`.

**AP reservoir, R006:** for every fixed reduced class `u mod M` and every fixed `0<θ<1/2`,

\[
 \#\{x<p\le2x:p\equiv u\pmod M,\ P^+(p-1)>x^{1-\theta}\}
  =(c(\theta)/\varphi(M)+o(1))N(x),\qquad
 c(\theta)=-\log(1-\theta).
 \tag{AP}
\]

This is a previously reviewed project result, not a statement silently inserted into the upstream PD theorem.

**All-q splitting bound, P:** for each fixed integer `|a|≥2`, there are `q₀(a), C_a` such that for every prime `q≥q₀(a)` and every real `x≥2`,

\[
 \#\{x<p\le2x:p\text{ splits completely in }\mathbb Q(\zeta_q,a^{1/q})\}
 \le C_a\left(\frac{x}{q(q-1)\log x}
       +\frac{x^{1-\delta}\log(2q)}{\log x}\right).
 \tag{S}
\]

I read P `sections/07-splitting.tex`, `spl:field-bounds`, `spl:smooth-estimate`, and the displayed bound preceding the final restricted-q specialization. The field degree is `q(q−1)` for sufficiently large q depending on a, including signed bases and perfect powers. The source's discriminant-to-degree bound and field-uniform smoothing give (S). P `sections/01a-reduction.tex`, `alg:splitting-test`, identifies `q|i_p(a)` with complete splitting when `p∤aq`. The all-q bound has already been derived and audited in R004/R006; it is not new work here.

The algebraic arguments below use cyclicity of finite fields, quadratic reciprocity, elementary Kummer theory, and the ordinary **fixed-field** Chebotarev theorem. No GRH is assumed. Fixed-field Chebotarev will only count the finite local conditions themselves; it will never be used to assert their independence from the large factor of `p−1`.

The following source hashes identify the most important actual upstream contracts. Full paths, immutable raw URLs, SHA-256 and Git-blob hashes for every download are in the adjacent `manifest.json` and `verification.json`.

- P `sections/07-splitting.tex`: SHA-256 `b8dc6a9385c2bf695544b5b81e8460dd053083f2346dc6a1d8a81f6dfc084a94`; Git blob `ee9b3eac0decd351991b6b3f8d2b237b5df2970d`.
- D `sections/06-correlations.tex`: SHA-256 `09d0d46506b82c0cc8c0f04d5c4ff39abe9b6699b7ab04078e73f759d6c46f1d`; Git blob `142bd62088b1471bc321c183129d4000a1476821`.
- D `sections/07-extraction.tex`: SHA-256 `975713ca85a0318b26b17886afae993052bf3525bb020b3498f5cbf04c835f49`.
- P `sections/08-type-ii.tex`: SHA-256 `97b1d9b0456a5951a25bbd9ee297da2c275a9c63e202aef139ad63e2c834794e`.

## 3. The sharp algebraic criterion is already known

First dispose of degenerate inputs. For an empty list the simultaneous condition is vacuous. If a nonempty list contains `0`, `1`, or `−1`, simultaneous primitive-root primes form at most a finite set. Hence take a finite nonempty set `A={a₁,…,a_k}` of integers with `|a_i|≥2`.

Let `Γ=⟨a₁,…,a_k⟩⊂Q*`, and let `Γ₂, Γ₃` be its images in `Q*/Q*², Q*/Q*³`. Define:

- **Q:** no product of an odd number of distinct listed bases is a rational square.
- When Q holds, the well-defined unique character `w₂:Γ₂→{±1}` is specified by `w₂(a_i)=−1` for every i.
- **F:** `[-3]∈Γ₂` and `w₂([-3])=+1`.
- **C:** there is a homomorphism `λ:Γ₃→F₃` such that `λ([a_i])≠0` for every i.

Moree–Stevenhagen Theorem 6.2, together with §5's quadratic obstruction, says exactly that the conjectural joint Artin density is positive if and only if

\[
             \mathrm{Q}\quad\hbox{and}\quad(\neg\mathrm{F}\ \hbox{or}\ \mathrm{C}).
             \tag{MS}
\]

The implication from this algebraic positivity to positive prime density in that paper uses GRH. We do not assume GRH or relabel (MS) as a newly proved unconditional density theorem.

Here are direct checks on the obstruction side. A primitive root at an odd prime is a nonsquare. An odd product of simultaneous nonsquares cannot be a square; this proves Q is necessary. If F holds, every prime at which all a_i are nonsquares has `(-3/p)=1`, hence `p≡1 mod3`, apart from finitely many excluded primes. At such a prime the cubic residue character on the subgroup generated by the a_i is a homomorphism to `μ₃`. If C fails, at least one a_i is a cube, hence cannot be primitive. Thus failure of (MS) is an actual finite obstruction, not just a possible zero value of a formal density.

Examples:

- `{a,b,ab}` fails Q whenever all three bases are allowed: the product of the three is `(ab)²`. In particular `{2,3,6}` is impossible at every odd unramified prime.
- A positive square fails Q by itself; a negative square does not. Signs are part of `Q*/Q*²`; they disappear in `Q*/Q*³` because `−1` is a cube.
- `{8,−24}` satisfies Q and F but fails C because 8 is a cube. This also shows why merely excluding individual positive squares is insufficient.
- `{5,−15,600,1029}` is the example already printed after Moree–Stevenhagen Theorem 6.2. Its four nonzero cubic vectors occupy all four projective directions in `F₃²`; their zero hyperplanes cover the dual plane. No individual base is a cube, yet C fails.
- `{2,−6}` satisfies Q, F and C. The cubic vectors can be taken as `(1,0)` and `(1,1)` in the coordinates 2,3, and `λ=(1,0)` is a valid witness. This is the simplest test case used below.

## 4. Complete realization lemma, with old-work attribution

**Lemma.** Suppose Q holds. There is a reduced class `u mod M₀` making every a_i a nonsquare and satisfying `u≠1 mod ℓ` for every prime `ℓ≥5` dividing `M₀`. The class can also be chosen with `v₃(p−1)≤1` throughout it. It can be chosen with `u≠1 mod3` if and only if F does not hold.

Here we may take `M₀=72∏_{ℓ≥5, ℓ|∏a_i}ℓ`. The claim about avoiding 3 refers to these simultaneous nonsquare classes; it is not a criterion for primitive roots in an arbitrary prescribed progression.

**Proof.** View squareclasses additively over `F₂`. The assignment `w₂(a_i)=−1` is consistent precisely when there is no odd relation among the a_i, namely Q. Extend this character to the vector space generated by `−1`, 2, 3, and all prime factors of the a_i. Such an extension can have `w(-3)=−1` exactly when F fails: if `[-3]` lies outside `Γ₂` its value is free; if it lies inside, its value is already fixed.

Choose a unit residue modulo 8 realizing the independently specified values `w(-1),w(2)`. The four residues `1,3,5,7` realize the four possibilities. For each odd support prime ℓ, quadratic reciprocity requires

\[
       (u/\ell)=w(\ell)\,w(-1)^{(\ell-1)/2}.
       \tag{QR}
\]

For `ℓ≥5`, either Legendre sign has a nonzero representative other than 1: in the square case there are `(ℓ−1)/2−1≥1` choices, and in the nonsquare case all `(ℓ−1)/2` choices avoid 1. For `ℓ=3`, the only nonzero representative other than 1 is 2; its sign is −1. Thus avoiding 1 at 3 is equivalent to `w(3)w(-1)=w(-3)=−1`. Apply CRT to the chosen residues.

If the chosen residue is 1 modulo 3, lift it to 4 or 7 modulo 9, giving `v₃(p−1)=1`. If it is 2 modulo 3 then `v₃(p−1)=0`. These lifts preserve all quadratic signs. Finally enlarge to `M₀` as displayed. Necessity in the last assertion follows from `(-3/p)=1` under F. This proves every claim. □

This proof is included to validate all dependencies and signs. Its substantive realization argument already appears in Anwar–Pappalardi Lemma 1 and in Moree–Stevenhagen's proof of Theorem 6.2. It is not a novelty-bearing result.

## 5. Strongest complete positive deductions obtained here

All statements in this section assume (AP) and (S), and assert a positive lower proportion in **every sufficiently large real dyad**, not merely along a subsequence. The proportional constants depend on A. No natural-density formula is claimed.

**Proposition 1 (universal bound two).** For every finite A with `|a|≥2` there are `c_A>0, x_A` such that for every `x≥x_A`,

\[
 \#\{x<p\le2x:p\nmid\prod_{a\in A}a,\quad i_p(a)\mid2\ \text{for all }a\in A\}
 \ge c_A N(x).
 \tag{B2}
\]

This improves R004's unspecified B to **2**, independent of A. The constant 2 cannot be replaced by 1 for all A, since `A={4}` is a counterexample. It is nevertheless a routine use of R006, not the requested new substantial theorem.

**Proposition 2 (exact quadratic criterion for indices 1 or 3).** Such a set A satisfies Q if and only if there exist `c_A>0,x_A` such that for every `x≥x_A`,

\[
 \#\{x<p\le2x:p\nmid\prod_{a\in A}a,\quad i_p(a)\mid3\ \text{for all }a\in A\}
 \ge c_A N(x).
 \tag{B3}
\]

When Q and `¬F` hold, the conclusion can be strengthened to `i_p(a)=1` for every a. Under Q alone, replacing `{1,3}` by `{1}` is false, as `{8,−24}` shows. This proposition completely isolates the remaining global obstruction at the prime 3, but its proof is also routine after R006 and the old realization lemma.

### Common sieve proof, with full parameter order

Fix nonempty A, choose any `0<θ<δ`, and fix the starting reduced class `u mod M₀` as follows.

- For B2 take `u=11 mod12`. Thus `v₂(p−1)=1` and `3∤p−1`.
- For B3 use §4's nonsquare class with `v₃(p−1)≤1` and avoidance of 1 at every support prime at least 5.
- For simultaneous index one under Q and `¬F`, use §4's nonsquare class additionally avoiding 1 at 3.

Choose an integer Y exceeding all `q₀(a)`, 3 and all prime factors of M₀. Keep **all** reduced classes above `u mod M₀` which avoid 1 at every new odd prime `q≤Y` not dividing M₀. Call their union `R_Y`, of modulus `M_Y`. Its prime-density weight is exactly

\[
 w(Y)=\frac1{\varphi(M_0)}
       \prod_{\substack{3\le q\le Y\\q\nmid M_0}}
                         \frac{q-2}{q-1}\asymp_{M_0}\frac1{\log Y}.
 \tag{W}
\]

For the last comparison divide each factor by `1−1/q`: the ratio is `1−1/(q−1)²`, with a positive convergent product over odd primes. Mertens' product estimate gives (W). For **each fixed Y**, summing (AP) over these finitely many classes gives

\[
 \#\{p\in R_Y\cap(x,2x]:P^+(p-1)>x^{1-\theta}\}
       =(c(\theta)w(Y)+o(1))N(x).
 \tag{R}
\]

On this reservoir write `p−1=mQ`, with `Q>x^(1−θ)` prime and `m<2x^θ`. For sufficiently large x, `Q>m`, so Q occurs just once. If Q divides any `i_p(a)`, then `ord_p(a)|m` and p divides

\[
       \prod_{1\le j\le\lceil2x^\theta\rceil}|a^j-1|.
\]

All factors are nonzero for `|a|≥2`, for either sign. The logarithm of this integer is `O_a(x^(2θ))`; consequently only `O_a(x^(2θ)/log x)=o(N(x))` primes above x can divide it. Sum over the fixed finite A.

Every other index prime divides m. For `Y<q<2x^θ`, (S), the splitting test and a union bound give, with a constant `C_A` independent of Y and x,

\[
 \#\{x<p\le2x:\exists a\in A,\ \exists\text{ prime }q\in(Y,2x^\theta),\ q\mid i_p(a)\}
 \le (C_A/Y+o(1))N(x).
 \tag{Tail}
\]

Indeed the main terms are bounded using `∑_{n>Y}1/[n(n−1)]=1/Y`; the total errors are `O_A(x^(1−δ+θ))=o(N(x))`. This is a global upper bound, with no conditioning on R_Y and no assumption that the individual Kummer fields are independent.

Choose Y **once** so large that `C_A/Y<c(θ)w(Y)/8`. This is possible by (W). Freeze Y and the entire modulus before taking x to infinity. Eventually the reservoir contains at least `3c(θ)w(Y)N(x)/4`, the middle exception at most `c(θ)w(Y)N(x)/4`, and the large-Q and finitely many ramified/base-prime exceptions together at most `c(θ)w(Y)N(x)/4`. At least `c(θ)w(Y)N(x)/4` primes survive.

For B2 every odd index prime has been removed, and `v₂(p−1)=1`, hence `i_p(a)|2`. For B3 nonsquareness removes 2, every index prime at least 5 has been removed, and `v₃(p−1)≤1`, hence `i_p(a)|3`. Under Q and `¬F`, nonsquareness removes 2 and the class construction removes 3 as well, leaving index one. These arguments apply to every real `x` beyond a fixed threshold. Summing dyads gives positive cumulative lower density as well.

Necessity in B3 is elementary: an odd residual index means the exponent of a relative to a primitive root is odd, hence a is a nonsquare. An odd square relation forbids simultaneous nonsquares at all odd primes not dividing the bases. The empty set in B2 is immediate. This completes all assertions. □

There is no new estimate hidden in this proof. The prime-index decomposition, large-Q product, middle-tail summation and `1/log Y` class union are all R006's mechanism. Its reuse for many bases just changes `C_a` to `C_A`. B2/B3 should not be promoted to the requested second substantial finding merely because their statements are stronger than R004.

## 6. A complete obstruction to finite-progression encoding of the remaining case

Let `A={2,−6}`. Simultaneous nonsquareness forces

\[
      (-3/p)=(2/p)(-6/p)=1.
\]

Thus `p≡1 mod3`. More explicitly, the simultaneous nonsquare primes outside 2,3 are precisely `p≡13,19 mod24`.

Put

\[
 L=\mathbb Q(\zeta_3,\sqrt[3]2,\sqrt[3]3),\qquad E=\mathbb Q(\zeta_3).
\]

**Proposition 3.** For every fixed modulus M divisible by 24 and every reduced class b whose reduction modulo 24 is 13 or 19, exactly a relative density `4/9` of primes `p≡b mod M` have both 2 and −6 noncubes modulo p. Both the cubic-good and cubic-bad subsets have positive density in every such progression. Therefore no nonempty finite union of compatible arithmetic progressions forces the two noncube conditions, even after deletion of a zero-relative-density exceptional set.

More quantitatively, on the set of simultaneous nonsquare primes, any Boolean periodic function has asymptotic classification error at least `4/9` for this cubic-good indicator. Thus enlarging a fixed modulus cannot even make these conditions arbitrarily well approximated in prime relative measure.

**Proof.** The classes of 2 and 3 are independent in `Q*/Q*³`, by their valuations. They remain independent over E: if a rational number is a cube in a degree-2 extension, its norm shows that its square is a rational cube, so the number itself is a rational cube. Consequently Kummer theory gives `Gal(L/E)=V≅F₃²` and `[L:Q]=18`.

Complex conjugation fixes the real cube roots and sends `ζ₃` to its inverse, so

\[
       \operatorname{Gal}(L/\mathbb Q)=V\rtimes\langle c\rangle,
             \qquad cvc^{-1}=-v.
\]

Its commutator subgroup is V: commutators with c give `−2v`, which ranges over V, and the quotient by V is abelian. Hence its maximal abelian subfield is exactly E. For `F=Q(ζ_M)`, which contains E, it follows that `L∩F=E`. Indeed the intersection is Galois and abelian over Q and so lies in the maximal abelian subfield of L.

The automorphism `ζ_M↦ζ_M^b` fixes E because `b≡1 mod3`. In `Gal(LF/Q)` the fiber above this automorphism consequently consists of all nine translations `v=(s,t)∈F₃²`. Chebotarev counts the conjugacy-stable good subset of this fiber by its cardinality; the individual nonzero translations need not be rational conjugacy classes, but pairs `{v,−v}` are, and the conditions below are invariant under this pairing. The whole fiber has density `1/φ(M)`.

At a prime above p, the cubic residue characters of 2 and 3 have exponents s,t. Since −1 is a rational cube, that of −6 has exponent `s+t`. Thus the good translations are those with

\[
          s\ne0,\qquad s+t\ne0.
\]

There are four: `(1,0),(1,1),(2,0),(2,2)`. Their density is `4/(9φ(M))`; the other five have density `5/(9φ(M))`. The prime-density ratio is therefore exactly `4/9` in every compatible class.

For any periodic Boolean approximation refine its period with 24. On each compatible reduced class it predicts either 0, making errors on a fraction `4/9`, or 1, making errors on a fraction `5/9`. Summing the finitely many class asymptotics proves the last assertion and the impossibility claim. □

This is an obstruction to a **specific proof route**, not a counterexample to simultaneous Artin and not a proof that the accepted corpus cannot imply the desired theorem. In fact 13 and 19 are small primes where both bases are primitive roots. The algebraic density in (MS) is positive.

### Why the usual reservoir subtraction does not repair this

Even a perfect ordinary Chebotarev asymptotic leaves a cubic-bad fraction `5/9` in these classes. The large-factor reservoir from R006 has relative mass `c(θ)<2·10^-6` for `θ<δ`. Separate knowledge of these two marginals gives only the Fréchet lower bound

\[
       \max(0,c(\theta)+4/9-1)=0
\]

for their intersection. One can explicitly couple a Bernoulli event of mass `c(θ)` wholly inside the bad set of mass `5/9`, while preserving both marginals. The same construction can be made in every progression. This demonstrates the logical deficiency of the marginal-information argument; it is not a model of the actual primes or of all the lower-level corpus assumptions.

Increasing Y makes the class union and its cubic-bad subset smaller by the same weight w(Y); it does not turn the fixed cubic obstruction into the `O_A(1/Y)` tail. Applying the all-q estimate at q=3, where valid, has no power-saving main term either. No choice of fixed Y repairs this loss without new joint information.

## 7. The stronger feasible target actually isolated

The remaining **global** case can be reduced to cubic Kummer fields alone; an arbitrary nonabelian Chebotarev-PD theorem is more than is needed.

Suppose Q and F hold and C is true. Let `r=dim_F3 Γ₃` and

\[
       H=\{\lambda\in\operatorname{Hom}(\Gamma_3,\mathbb F_3):
                     \lambda(a_i)\ne0\text{ for every }i\},\qquad h=|H|>0.
\]

Here r≥1. Set `L_A=Q(ζ₃,a₁^(1/3),…,a_k^(1/3))`. The norm argument and conjugation calculation of §6 give

\[
       \operatorname{Gal}(L_A/\mathbb Q)
           \cong\mathbb F_3^r\rtimes C_2,
       \qquad L_A\cap\mathbb Q^{\rm ab}=\mathbb Q(\zeta_3).
       \tag{Cubic}
\]

Under F, §4's nonsquare starting class has `p≡1 mod3`. Adjoin avoidance of 1 at every prime `5≤q≤Y` as in §5. Ordinary fixed-field Chebotarev and (Cubic) imply that the density of the additional local condition “every a_i is a noncube” in this union is exactly

\[
                  (h/3^r)\,w(Y).
                  \tag{Local}
\]

This proves that there is **no further finite realization obstruction** in this branch. It does not establish the following genuinely stronger distribution assertion:

**Unproved target CR.** For every fixed reduced class `u mod M` with `3|M`, `u≡1 mod3`, every such fixed cubic field L_A and its nonempty inversion-stable set H, and fixed `0<θ<δ`,

\[
 \frac{\#\{x<p\le2x:p\equiv u\pmod M,
     P^+(p-1)>x^{1-\theta},\quad
     \operatorname{Frob}_p(L_A/\mathbb Q)\subset H\}}{N(x)}
       \longrightarrow
       \frac{c(\theta)}{\varphi(M)}\frac{h}{3^r}.
       \tag{CR}
\]

It would suffice to prove a positive lower bound here with a common explicit factor depending on θ and A but **not deteriorating with the later small-prime-avoidance modulus**. Unknown positive constants for each modulus do not close the Y choice.

**Verified implication, not an achieved theorem:** CR, combined with (AP), (S) and the proofs above, establishes positive lower proportion of simultaneous primitive-root primes exactly under (MS). Indeed summing CR over the fixed union gives `c(θ)(h/3^r)w(Y)`, which beats `C_A/Y` for large fixed Y. Nonsquareness removes 2, noncubicity removes 3 even if its valuation in p−1 is larger than one, congruences remove `5≤q≤Y`, and the old two exceptions remove all larger index primes. Every algebraic and parameter-order step of this implication is supplied here; CR itself is not proved.

For the concrete pair `{2,−6}`, the target is already nontrivial with `h/3^r=4/9` and classes 13 or 19 modulo 24. Establishing this instance would be materially beyond another finite-base union bound. The main global theorem needs CR in those classes with all further fixed small-prime exclusions, not only at modulus 24.

### Actual attempted analytic extensions and their unresolved steps

I checked the underlying source contracts, rather than stopping at the observation that R006's final statement is abelian.

1. **Insert a Frobenius weight into the second core.** D `thm:two-sided` explicitly requires `G(n)=G(n_*)`, where all active prime powers are removed. A completely multiplicative extension f of a nonconstant prime Frobenius weight gives `f(D_R(w+D_C))=f(D_R)f(w+D_C)`, and leaves a shared-label factor. This is precisely what the invariant-core hypothesis excludes. A Frobenius indicator is defined only at primes until an extension to composites is supplied; assigning it arbitrarily on composites does not cure this equation.
2. **Use R006's two-endpoint device.** Its residue identity depends on subtraction of two congruences forcing a unique scalar `D_R≡D_C^(-1) mod M`. There is no analogous additive identity for cubic Frobenius of rational primes. For a unit-valued completely multiplicative f, inserting conjugate weights at both endpoints cancels f(D_R), but the raw term becomes `f(w) conjugate(f(w+1))F_x(w)G(w+1)`, with an unwanted factor at w. The source endpoint-energy estimate is for the unweighted centered F_x, and extraction seeks a weight at p, not this relative weight at p−1 and p. Neither step has been justified by this cancellation.
3. **Choose active primes that split in the cubic field.** This would make f equal to 1 on the active primes and restore the formal invariance. But D §6 requires every big group to be **all primes in an interval**; §7's selection and extraction also use full candidate intervals. Chebotarev-selected groups do not satisfy those contracts. A proof would have to extend the ideal-family/comparison estimates, marking model, selection, and deweighting together, with constants controlled before the later parameters. Positive Chebotarev density of a group is not that proof.
4. **Exploit P's more general coefficient-transfer lemma.** P `lem:marked-coefficient-transfer` really does allow a new scalar sequence if its character–Mellin sums save every fixed logarithmic power through `|t|≤2XL^B`, for every logarithmic-modulus character. But it also retains the invariant F and marked group hypotheses. A new Frobenius-weighted prime-minus-rough coefficient requires a correctly normalized rough model, a verified scalar estimate, and extraction compatible with its extension to products. Fixed-field Chebotarev alone verifies none of those full interfaces. The accepted Hecke strip suggests a possible tool for the scalar estimate, but does not remove the active-group/invariance problem.

These are specific gaps in attempts, not universal impossibility results. No theorem extending these interfaces is asserted here. The mathematically useful next assignment is CR for elementary cubic Kummer extensions, with an independent review of the new correlation/extraction argument if it is found. Repeating only the known quadratic/cubic feasibility calculation would not advance this target.

Prescribed progressions and mixed order constraints enlarge this challenge: a class can force `p≡1 mod ℓ` for any fixed odd ℓ, and prescribed positive indices can require higher prime-power Kummer splitting. The exceptional role of 3 above depends on being free to choose the global progression. It must not be asserted for every prescribed progression. Järviniemi–Perucca's already-existing GRH framework also rules out claiming novelty merely for writing those mixed constraints as a finite automorphism problem.

## 8. Finite falsification checks and integrity

Run `python3 frontier/experiments/i05_joint_artin/check.py`. The script uses exact integer arithmetic and the Python standard library. Its adjacent `results.json` records:

- 2,516 quadratic linear-system cases, 2,516 avoidance-of-3 certificate cases, and 2,516 capped-3 class cases, using every subset of size at most four from a fixed pool of 16 signed/power bases. All agree with direct reduced-residue enumeration.
- 415,888 reciprocity checks against Euler's criterion at actual primes, with no failure.
- Exhaustive enumeration of the nine translations in `F₃²`: precisely four satisfy the two noncube conditions for `{2,−6}`. The four projective zero hyperplanes cover all nine vectors, verifying the finite mechanism in the classical four-base counterexample.
- Below 300,000, the classes 13 and 19 modulo 24 have respectively 3,265 and 3,243 primes; 1,432 and 1,439 satisfy both noncube conditions. Each class has both good and bad primes: first examples are 13/37 and 19/43. These counts do not establish the limit 4/9; §6 proves that by fixed-field Chebotarev.
- 184,883 finite base–prime survivors of the bound-two elimination and 172,008 of the bound-three elimination, with no failure. A simultaneous test with 22 signed/perfect-power bases has 3,794 primes with every index at most two; the bound is nonvacuous. These are finite group-logic checks, not numerical verification of the very small exponent `θ<10^-6` or of any positive-density assertion.

All immutable upstream downloads are verified by recomputing `SHA1("blob "+length+NUL+bytes)` against the complete pinned tree as well as recording SHA-256. The source manifest distinguishes an unsuccessful HTML challenge-page retrieval of Lenstra's paper from the successful author's PDF; the latter is the one actually read. A university mirror of Järviniemi–Perucca returned HTTP 403, so the actual publisher's HTML theorem/proof was read and saved through the web tool. These retrieval failures have no mathematical content. `input-hashes.json` snapshots the earlier project reports used as premises. `artifact-manifest.json` records this round's outputs.

## 9. Vulnerable steps and final assessment

The complete proofs should be checked at: (i) the extension of w₂ including the sign and the prime 3; (ii) the distinction between bounding the valuation of `p−1` and removing a prime divisor of an index; (iii) the fixed-Y `w(Y)≫1/log Y` budget; (iv) the Kummer degree and maximal abelian subfield in (Cubic); and (v) the conjugacy stability needed to count four out of nine translations rather than erroneously treating individual nonzero translations as rational conjugacy classes. No unresolved gap is knowingly left in Propositions 1–3, but no fresh independent reviewer was invoked by this sub-agent.

**Honest verdict:** the arbitrary-base *algebraic* criterion is prior art. R006 proves its `¬F` branch routinely. The F-and-C branch remains an analytic joint-distribution problem; `{2,−6}` is an explicit compatible case for which this report does not prove positive proportion. The obstruction to replacing its cubic condition by finite progressions is complete and quantified. B2/B3 are useful, fully proved alternatives and sharp in the limited senses stated, but they do not meet the user's nonroutine-novelty gate. CR is a concrete, stronger, plausibly useful next target, not a theorem delivered by this round. No claim of worldwide priority, full simultaneous Artin, positivity in every reduced class, or completion of the research objective is made.
