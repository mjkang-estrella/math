# H007 structured solver proposals: raw Claude Opus report

Unverified proposer claims; root objections and independent reviews control acceptance. No experiment authorized. Raw claims about divisibility, decoding exceptions, yields, tensor universality and proposed pilot capacity are not accepted merely by retention.

I wrote no files and ran no experiments, numerical scratch work, or child agents. I didn't read any other H007 proposal. Verified improvement remains **NONE**; the reference is still the classical square-root algorithm with known automorphism constants.

## A yardstick every card below is checked against

This is a cost argument about the named primitives only, not a generic lower bound. When m factor-base points from a set F of size B ≈ q^{1/m} are summed and compared with one target, each (tuple, target) pair is a relation with probability about c/q.

- **Enumerating pairs one by one** costs 1 per pair.
- **One "free" elimination** removes one variable restricted to a set with a sparse vanishing polynomial, such as the coset u+μ_B. It uses a gcd or norm Res_s(g, s^N−1) at polylog cost. This saves a factor of up to that set's size.
- **A hash join or dense product-tree resultant** costs the sum of the list sizes.

With only one free elimination per test, as in D1 (the existing diagonal-orbit gcd card) or any pointwise-plus-norm scheme, each relation costs about q/B. B relations then cost Θ(q) whatever m is.

With e free eliminations, the total is q/B^{e−1} plus about B² of sparse linear algebra. Tying the square-root reference needs e ≥ 3 at m = 4. Beating it needs e ≥ 4 at m = 5, giving q^{2/5}.

Any new selector therefore has to cover at least B³ tuples per test at sub-B cost. Covering more targets at once does not help unless the target set has a sparse vanishing polynomial and known logarithms. A compact program (straight-line program, SLP) for the vanishing polynomial of a group arithmetic progression would itself solve the discrete log by bisection.

## Card 1 (lead): Graeffe–Riemann–Roch symmetric chain, "GRR"

**Mechanism.** Take B = b^k dividing p−1 and V = u+μ_B. For a target R = aG+bQ, parametrise every decomposition R = P1+…+Pm by functions f in L((m+1)O) with f(−R) = 0. That is an affine chart in m−1 coefficients α.

- The norm N(f) = A(x)² − (x³+ax+b)·B(x)², divided by (X − x(R)), is h_α(X) = ∏(X − x(P_i)). Its coefficients are **quadratic** in α.
- Shift X → X+u.
- The subgroup condition becomes "h divides X^B − 1". That holds exactly when Graeffe^k(h) = (X−1)^m. For b = 2 the Graeffe step is g_{j+1}(X²) = ±g_j(X)·g_j(−X).
- The system is then m(k+1) quadratic equations in (m−1)+mk unknowns: α plus m chain coefficients per layer. Solve it with Gröbner/F4, or with a dedicated triangular solver.
- Any solution with x in F_p gives y = −A/B in F_p directly. So there are no invalid-x or sign branches, and the m! permutation symmetry disappears.
- Verify the relation with actual group arithmetic, collect about B relations, then run sparse linear algebra.
- For general p, use PKM's isogeny chain on an auxiliary curve E′ (Vélu factors), applied to the whole divisor rather than per variable.

**Where the gain could come from, and the barrier.**

- The degree-2^{m−1} summation polynomial S_{m+1} is replaced by quadratic norm equations.
- PKM's per-variable chains x_i^{p_j} are replaced by one symmetric chain on the elementary symmetric functions. Solutions shrink by about m!, and the per-variable degree blow-up goes away.
- The barrier is the solving degree D. A D that stays bounded in k would make point decomposition polylog and the total about q^{2/m}. A D that grows with k makes the method B^{Θ(1)}.
- PKM's own Table 4 (p−1 subgroups) shows times rising roughly 6–8× per doubling of B, i.e. a slope of about 2.7 in B. That is worse than Õ(B) norm enumeration, so the bar is concrete.

**Total predicted cost.** (m!·q/B^{m−1})·T_GRR(k) plus B²·m linear algebra, plus O(1) relation verification per hit.

- T_GRR is the cost to find the system's O(1) solutions, or to certify none.
- Failure fraction is about 1 − 1/m!, already inside the first term.
- Memory is the Gröbner matrix size, about C(n+D, D) with n ≈ m·log_b B, plus B factor-base entries.
- There is no setup beyond finding μ_B, or for general p, E′ and its isogeny chain.
- It wins only if T_GRR ≤ q^{1/2−1/m}/m!, roughly B^{m/2−1}, with m ≥ 5.

**Prior-art distinction.**

- **PKM** [inspected: https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf]: per-variable chains, Gröbner on S_{m+1} plus the L_j maps, complexity explicitly left open. My reading of its experiment tables is that they use m = 2, with no symmetrisation and no Riemann–Roch norm.
- **YYTK** [inspected: https://nutmic2019.imj-prg.fr/confpapers/SemaevECDLP.pdf]: lower bound of about m·d^{m−1} for the ideal ⟨S_{m+1}, F(x_i)⟩, conditional on genericness assumptions. That ideal is not the GRR ideal; the bound would need re-deriving for it.
- **Huang–Kosters–Yeo** [inspected: https://eprint.iacr.org/2015/573]: first-fall-degree heuristics are unreliable, so no D-bound may be assumed.
- **Semaev 2015** [inspected abstract: https://eprint.iacr.org/2015/310]: binary-field split equations.
- Symmetrised summation polynomials (Faugère et al.; https://hal.archives-ouvertes.fr/hal-00935050) and Graeffe root finding (Grenet–van der Hoeven–Lecerf) appeared only in search results and were **not inspected**.
- I found no source combining the Riemann–Roch norm with a divisor-level Graeffe chain. That is not proof of novelty.

**Unsupported assumption.** D, or the cost of a dedicated triangular solve, grows slower than (m/2−1)·log B.

**Cheapest decisive falsifier.**

- Toy primes with 2^k dividing p−1. Run m = 2, 3, 4, 5 with B^m ≈ m!·p, k = 2…8, and 50 targets per cell under declared seeds.
- Record the maximum F4 degree, matrix dimensions, field operations and solution counts.
- Run the identical instances in PKM's per-variable formulation, and as Õ(B) norm enumeration.
- **Kill** if the fitted cost slope in B is ≥ 1 at m = 2–3 (i.e. it loses to enumeration). **Kill** if the slope is ≥ m/2−1 at m = 4–5, or if D rises by ≥ 1 per 2 layers.
- This fits within the 60-second / 1M-event cap at small k.

## Card 2: two-coset bivariate norm sieve with large-prime recovery (retained as a loser)

**Mechanism.** This is the concrete alternative selector the brief asked for.

- Run a D1 orbit (x_i = u + c_i·t, t in μ_B), with the residual point required to lie in a large structured set F_L = {x in w+μ_N}.
- For each t, compute the norm Res_s(S_{m+2}(…, w+s, z), s^N − 1) in polylog. That costs Õ(B) per orbit and covers B·N pairs.
- Merge partial relations through shared large primes, single or double.

**Cost.** Each partial relation costs about q/(2^{m+1}·N). Recovering B full relations needs about √(2NB) partials, for a total of about q·√(B/N). Even at N ≈ q this is ≥ √(qB). With only small-base pairs, the total is Θ(q).

The same accounting kills two variants:
- weighted small-scalar factor bases (Σ k_i·P_i = L·R), which add tuples but not tuples per test;
- multi-target batching through a dense product-tree resultant.

**The exact missing primitive.** Find μ_B × μ_N points on a low-degree plane curve f(t,s) = 0 in time o(min(B,N)). The special case "ζ in μ_B with ζ+1 in μ_N" is the gcd of two sparse high-degree polynomials. I know of no sub-min algorithm.

**Falsifier.** None needs to be run: this is rejected on paper, and reopening requires that primitive.

**Prior art.** Large-prime variants of decomposition index calculus over extension fields (Gaudry/Diem; not re-inspected here) and the H006 D1 card.

## Card 3: the dense TT obstruction extends to every factor-base set V, including structured ones

This is negative evidence that narrows the implicit-representation lane rather than a winning mechanism. It addresses the brief's note that the reviewed obstruction "is not universal over structured V."

**Argument.**

- Pick any V of valid x-coordinates with |V| = B, structured or random, and a uniformly random target R.
- Use exponents t ≤ (|V|−1)/16. F = S6(x, y, c1, c2, c3, z) has degree 16 in x and in y, so F^t has degree ≤ 16t in each.
- Because |V| > 16t, the Vandermonde matrices on V have full column rank. So rank[F^t(v_i, v_j)] equals the coefficient separation rank, which is ≥ t+1 by the reviewed vanishing-order lemma.
- The generic-specialisation condition on (c1, c2, c3) is a bounded-degree open condition. Schwartz–Zippel on the product grid V³ bounds the bad fraction by O(1/|V|), and z random adds O(1/q).
- Any addition chain to p−1 visits some exponent t in [r′, 2r′), with r′ ≈ |V|/32.
- By the symmetry of the two middle cuts, the middle core has rank Ω(B²)·B, i.e. Ω(B³) ≈ q^{3/5}/1024, for every V, deterministically in V. The draft's Schwartz–Zippel step over random V is only needed for its larger-t range.

**What survives.** Only representations that avoid dense entrywise powers: implicit cores, non-power zero tests, or GRR-type algebraic solving (Card 1). On μ_B grids, the "sparse coefficient-basis" escape fails too. Entrywise powers become convolution powers in F_p[Z_B^m], and their support fills B^m once t is of order B.

**Unsupported assumption / falsifier.** Write out on paper the constant 16 and the bad-locus degree for (c1, c2, c3) in S6. If an independent reviewer finds the bad locus contains V³ for a structured V, then that V escapes the obstruction.

## Five-item report

1. **Best supported work:** unchanged classical square-root reference.
2. **Verified improvement:** NONE.
3. **Hypothesis to test:** GRR (Card 1), specifically whether the solving degree of the symmetric Graeffe/Riemann–Roch chain stays sub-linear in log B.
4. **Evidence:**
   - Against: PKM's per-variable data degrades steeply, and HKY warns against fall-degree heuristics.
   - For: the system is all-quadratic, symmetry-free and has no invalid-x branches, a structure PKM and YYTK did not analyse.
   - Cards 2 and 3 are paper rejections of named schedules.
5. **Next decisive step:** run Card 1's toy F4 slope comparison against PKM's formulation and against Õ(B) enumeration, at m = 2–5 under fixed seeds.

**Sources:**
- [PKM, PKC 2016](https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf) (inspected)
- [YYTK](https://nutmic2019.imj-prg.fr/confpapers/SemaevECDLP.pdf) (inspected)
- [Huang–Kosters–Yeo 2015/573](https://eprint.iacr.org/2015/573) (inspected)
- [Semaev 2015/310](https://eprint.iacr.org/2015/310) (abstract inspected)
- [Symmetrized summation polynomials](https://hal.archives-ouvertes.fr/hal-00935050) (search result only)
- [Galbraith–Gebregiyorgis 2014/806](https://eprint.iacr.org/2014/806) (search result only)
- [Vitse Fukuoka 2013 talk](https://www-fourier.univ-grenoble-alpes.fr/~viva/research/talks/Vitse_Fuku13.pdf) (search result only)
