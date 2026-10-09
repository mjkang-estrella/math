# H043 trace-scalar Opus raw report — UNACCEPTED

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h043-trace-scalar-construction-opus-20261009-r1`.
Provider/model: claudeAgent / claude-opus-5-5. Terminal result.
All new claims require independent review; this report admits incomplete required reading.
No executable experiment or new attack claim is accepted.

# H043 trace-family bridge pass: no new operator

I'm submitting no mechanism cards. The best supported ordinary-curve exponent is still 1/2, and verified improvement is still **NONE**.

I found no bridge from the trace family to the scalar k. The main reason is simple. The aligned exact-trace operator's output is a public function of the public lag point T itself, so any bridge would need the composite map n ↦ H(x([n]G)) to respect E's group law. I checked four bridges below, and none supplies that. Two points may be worth adding to the record: an explicit Weierstrass model for E'_b, and that reduction.

**What ran and what I read**
- I ran as Claude Opus 5.5 (`claude-opus-5-5`, 1M context).
- I read RESEARCH_LOOP.md, RESEARCH_TEAM.md, the H041/H042 lines in STATE.md, the H042 nonlinear-signals disposition and the Fable raw report.
- I did not open the H041 dispositions or the other H042 dispositions the brief names. Everything below rests on the nonlinear-signals material.
- I read no H043 proposals. I made no edits, ran no solvers or experiments, imported nothing executable, started no children and made no commits.
- Fresh primary reads, done with `curl | pdftotext` into a temporary directory that I deleted afterwards:
  - [Diem, arXiv math/0606607](https://arxiv.org/pdf/math/0606607): abstract and section 1.
  - [Fouvry–Kowalski–Michel, "A study in sums of products", arXiv 1405.2293](https://arxiv.org/pdf/1405.2293): Definitions 1.2–1.3, Theorem 1.5 and Definition 2.1.
- Access problems:
  - [ePrint 2004/153 (GTTD)](https://eprint.iacr.org/2004/153) returned an HTML challenge page, so I relied on Diem's restatement of that result.
  - My first two guessed arXiv IDs pointed to unrelated papers and were discarded.
  - I did not freshly read Semaev, Galbraith–Hess–Smart or Sutherland's class-polynomial work; any mention of them below is not from a fresh read.

## 1. The output depends only on the public point T (reduction, not an impossibility claim)

In the disposition, A = −[2⁻¹]T, so 2A = −T and b = x(2A) = x(T). The whole h-sum is therefore

Φ(T) = −a′_p(E′_{x(T)}) − χ(−1) − 2χ(x(T) − x([2⁻¹]T)),

which is a deterministic public function of T = [(c−1)k]G.

So querying it at affine images of Q tells you nothing beyond those points, which are already public. In effect it is a hash H(R) = a_p(E′_{x(R)}) of known points. The raw report's "range ≈ 4√p, so two or three queries determine k" is just a statement that this hash is roughly injective. It decodes only by inverting n ↦ H(x([n]G)).

A scalar bridge would need H to be compatible with E's group law. The missing construction is exactly that: either an efficient relation linking H(R), H(S) and H(R±S) (or H([c]R)), or a homomorphism from E(F_p) into something the trace arithmetic controls.

## 2. Explicit model for E′_b (fills the disposition's "paid model conversion")

This is root-checkable by hand. Substitute x = b − 1/s and V = W/s² in V² = (b−x)f(x). By Taylor expansion, using f″(b)/2 = 3b:

- W² = s³f(b−1/s) = f(b)s³ − f′(b)s² + 3b·s − 1.
- Then set t = f(b)s and Y = f(b)W:

E′_b ≅ Y² = t³ − f′(b)t² + 3b·f(b)·t − f(b)²,

valid for every b with f(b) ≠ 0.

The roots are t_i = ∏_{j≠i}(b − e_j). The λ-invariant is the cross-ratio of (b; e₁, e₂, e₃), which is Möbius in b, so j(E′_b) is a degree-6 rational function of b.

So H is the Legendre/X(2)-family trace pulled back to E. By the Hasse–Witt coefficient formula, H(b) mod p is a polynomial in b of degree at most (p−1)/2. Conversion costs O(1) field operations, but that changes no conclusion.

## 3. Bridges examined, each failing at a named step

**B1. Embed into J_b = Jac(C_b) and run index calculus.**
- C_b has rational points (0, ±y_R) lying over ±R. π*Q = [k]π*G inside J_b, so this is a genuine scalar bridge.
- Cost: Diem's theorem gives Õ(p^{2−2/g}) = Õ(p) for genus 2, against roughly √p for rho on E. Diem's hypotheses also require a cyclic class group or a known group structure.
- Memory is Õ(p^{1−1/g+1/g²}) = Õ(p^{3/4}).
- It loses on that upper-bound exponent. This is a comparison with the known algorithm, not a lower bound.

**B2. Use the gluing correspondence to transport R into E′_b.**
- Write σ, τ for the involutions with quotients E and E′_b. Then τ = ισ, so (1+τ) annihilates the image of (1+σ).
- C → E′_b is branched at the two points at infinity, so π′* is injective. Together these give π′_*∘π* = 0 exactly.
- Concretely, both lifts of R land on (0,0). The correspondence carries no copy of R into E′_b.

**B3. Look for equal-trace collisions and use the connecting isogeny as a certificate.**
- With about p^{1/4} trace computations you expect a collision H(R₁) = H(R₂). The two curves are then isogenous.
- The connecting ideal class lives in a class group that changes from collision to collision. No map from it to n₁ − n₂ is known, so relations don't accumulate.
- Missing step: that homomorphism. I don't claim it is impossible.

**B4. Use small-CM or supersingular fibres as distinguished points or a factor base.**
- Z_D = {R : E′_{x(R)} has CM by discriminant D}. This needs H_D(j(b)) = 0, giving at most 12h(D) points, computable by building H_D and finding its roots.
- These are explicit points with unknown logs. Using them as a factor base needs a decomposition algorithm over a set with no small-root or subspace structure, and none was supplied.
- Cheapest decisive check: a paper attempt to solve the summation polynomial restricted to these roots faster than enumerating tuples.

**Translation/dilation-statistic decoders: scoping sketch, unreviewed.**
- The pulled-back sheaf on E has unipotent ramification exactly at E[2].
- For S ∉ E[2], the translate t_S^*G is not isomorphic to G, even after a rank-1 twist. [c]^*G ramifies on E[2c].
- With SL₂-type monodromy, the Goursat–Kolchin–Ribet genericity (FKM Definition 2.1 is the analogue on A¹) would bound fixed-length translate correlations by roughly √p.
- This is an upper bound on statistical decoders only. It does not exclude a non-statistical bridge, and its monodromy hypotheses need a reviewer.

## Missing construction that remains

The gap is a relation or homomorphism compatible with the group law, connecting the arithmetic of E′_{x(R)} (its trace, End ring or class group) to the scalar of R. It must cost less than √q including calibration and verification.

Scope note: the trace identity is a full-group sum. For a prime-order curve, E(F_p) = ⟨G⟩. With a cofactor it is not a subgroup sum, although the reduction in section 1 holds either way.

Cheapest next check: a reviewer verifies the model in section 2 and the zero composite in B2 by hand.
