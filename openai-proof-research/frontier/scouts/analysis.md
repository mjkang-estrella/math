# Analysis / PDE / probability / mathematical-physics frontier scout

**Parent status: candidate under independent review, not an accepted finding.** Two follow-up tasks test correctness/novelty and the repeated-eigenvalue gap. The simple-eigenvalue condition is essential to the all-eigenfunctions claim; polygons and convex domains need not satisfy it. The maximum-set structure lemma is planar. The problem API's importance categories are distinct from MathDB's numerical news significance scores. The scout's original self-assessment below is provisional.

Date: 2026-10-08. Upstream: `openai/math` at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Every theorem in that revision is
accepted as true, as the user instructed. Every deduction below is checked
independently here. No first-pass finding (F001–F010) or archived proposal
is reused; none of them concerns the hot-spots problem.

Source catalogue: [`frontier/sources/analysis-CATALOGUE.md`](../sources/analysis-CATALOGUE.md).
Local copies: `frontier/sources/analysis-upstream/` (79 manuscript `.tex`/`.bib`
files) and `frontier/sources/analysis-mathdb/` (MathDB API records). Fetch
script: `frontier/experiments/analysis_mathdb_fetch.py`.

## 0. Outcome in one paragraph

**Main result (Section 2).** This is a new bridge lemma plus a proof. It
extends the corpus's smooth-domain hot-spots theorem (family 369) to
**every bounded simply connected planar Lipschitz domain whose first
positive Neumann eigenvalue is simple**. This includes simply connected
polygons (convex or not) and bounded convex planar domains **when that
eigenvalue is simple**.
For these domains, every first-positive eigenfunction attains neither its
maximum nor its minimum in the interior. For *every* bounded simply
connected Lipschitz domain, at least one nonzero first-positive
eigenfunction has this property. Every eigenfunction in its "limit set"
also has no strict local extremum and no nondegenerate critical point.

The new ingredient is a variational *separation lemma* (Lemma R). The
level set of an interior global maximum of a first-positive Neumann
eigenfunction cannot disconnect the domain. This lemma eliminates the
degenerate "ridge" maxima that a limiting argument from smooth domains
cannot exclude. Together they give a meaningful new case of the
AIMPL/Burdzy simply connected hot-spots conjecture, which MathDB lists as
named problem 384597.

**Remaining gap.** The case of an accidentally double eigenvalue is not
closed; Section 2.7 states it precisely. Section 3 records the ranked
targets that were screened, with obstructions. Section 4 lists entries
already answered directly by the corpus, which are not findings of this
scout.

## 1. MathDB ranking data actually visible

**How the data was retrieved.** I used the public read-only JSON API
(robots.txt allows crawlers on public pages):

- `https://mathdb.com/api/posts?importance=<tier>&limit=100&offset=…`
- `https://mathdb.com/api/posts/<number>`

**The tier scale.** MathDB shows a categorical *importance* field with
labels taken from its JavaScript bundle:

> landmark ("Millennium Prize") > celebrated ("A famous named problem,
> recognised well beyond its own field") > erdos > named > corpus.

No numeric significance score was found in these problem API records;
MathDB separately exposes numerical significance scores for news developments.
`vote_count` (mostly 0) and
`view_count` are popularity counters, not rankings, and I use no invented
scores. The landmark tier has 6 entries and the celebrated tier has 40;
both were downloaded in full (`landmark.json`, `celebrated.json`).

Top-tier entries touching this domain, with MathDB status as of the
retrieval:

| MathDB # | tier | title | MathDB status | status after accepting the whole corpus |
|---|---|---|---|---|
| 315852 | landmark | Navier–Stokes existence and smoothness | claimed_solved (user claim) | **open**; corpus 376 gives forced universal computation, not blowup or regularity (Section 3.1) |
| 315855 | landmark | Yang–Mills existence and mass gap | claimed_progress | **open**; corpus 215 is the 2D O(3)/O(4) σ-model (Section 3.6) |
| 315983 | celebrated | Kakeya conjecture | open | open for n ≥ 5; corpus 074 gives 3D maximal and 4D Hausdorff, and corpus already records dim ≥ 4 in ℝ⁵ (Section 3.3) |
| 315900 | celebrated | Invariant subspace problem | open | **open**; corpus 293 disproves the *hyper*invariant version only (Section 3.4) |
| 315873 | celebrated | Hilbert's sixteenth problem | open | uniform finiteness B(d) < ∞ proved (corpus 143, non-effective); values of B(d) and Smale's polynomial bound open (Section 3.5) |
| 315904 | celebrated | Sendov's conjecture | "solved" | not in corpus; Tao's large-degree theorem only; no corpus bridge found |

Named-tier entries used below: 384597 "Hot spots conjecture" (source AIMPL
shapesurface/3); 384598 "Directional hot spots"; 405813 "Polynomial bound
for limit cycles" (Smale); 398653 "Invariant subspace problem relative to
a von Neumann algebra"; 389103/389104 (Simon's Anderson problems).

MathDB also has 360825, a corpus-tier entry on hot spots for
simply-connected planar and convex domains. It is labelled "refuted", but
its own text says only that the source does not resolve it. I treat the
label as a database inconsistency.

## 2. Main result: strict hot spots on nonsmooth simply connected planar domains

### 2.1 Target and exact upstream input

**Target.** MathDB 384597
([API](https://mathdb.com/api/posts/384597); source
[AIMPL shapesurface 3](http://aimpl.org/shapesurface/3/)) states:

> "The first non-trivial Neumann eigenfunction does not have global extrema
> in the interior of Ω if (1) Ω ⊂ ℝ² is simply connected; (2) Ω ⊂ ℝⁿ (n ≥ 3)
> is convex."

Part (1) is Burdzy's conjecture
([Burdzy 2005, Conj. 1.2(ii)](https://arxiv.org/abs/math/0405472)). It
places no smoothness hypothesis on Ω. Part (2) is false for all
sufficiently large n by
[de Dios Pont, arXiv:2412.06344](https://arxiv.org/abs/2412.06344),
"Convex sets can have interior hot spots" (Dec 2024), which is not part of
the corpus.

**Upstream input (family 369).** Manuscript
`preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/`;
pinned text: [`sections/01-introduction.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/build/sections/01-introduction.tex).
`thm:main` says:

> Let Ω ⊂ ℝ² be a nonempty bounded simply connected open set with C^∞
> boundary, μ = μ₁(Ω) the first positive Neumann eigenvalue (Rayleigh
> infimum over mean-zero H¹), V its real eigenspace. For every 0 ≠ u ∈ V,
> ∇u(x) ≠ 0 for x ∈ Ω; in particular min_{∂Ω}u < u(x) < max_{∂Ω}u.

Note the C^∞ hypothesis. The manuscript explicitly separates its result
from domains with corners (triangles: Judge–Mondal) and from lip domains
(Atar–Burdzy). No other corpus family mentions hot spots; I grepped
`CONTENTS.md`.

**Notation.** For a bounded domain Ω, write μ(Ω) for the Rayleigh infimum
of ∫|∇v|²/∫v² over 0 ≠ v ∈ H¹(Ω) with ∫v = 0. Write E(Ω) for its
eigenspace when the infimum is attained. Minimizers satisfy
∫∇u·∇φ = μ∫uφ for **all** φ ∈ H¹(Ω), as recorded in the upstream
introduction. Eigenfunctions are real-analytic in Ω.

### 2.2 Definition (limit set)

Let Ω be a bounded simply connected planar domain with E(Ω) ≠ {0}. Define
L(Ω) as the set of u ∈ E(Ω) for which the following hold:

- there are bounded simply connected C^∞ domains Ω_k ⊂ ℝ²;
- every compact K ⊂ Ω lies in Ω_k for all large k;
- there are u_k ∈ E(Ω_k) with u_k → u uniformly on compact subsets of Ω.

L(Ω) is closed under real scalar multiplication.

### 2.3 Lemma R (maximum level sets do not separate) — new bridge lemma

*Hypotheses.* Let Ω ⊂ ℝⁿ be a bounded domain (no smoothness, no topology).
Let 0 ≠ u ∈ E(Ω). Suppose M := sup_Ω u is attained at some point of Ω, and
put S = {x ∈ Ω : u(x) = M}.

*Conclusion.* Ω \ S is connected.

*Proof.*

1. **Basic facts.** M > 0, because ∫u = 0 and u ≢ 0. If u ≡ M on an open
   set, analyticity gives u ≡ M, so −ΔM = μM and M = 0, which is
   impossible. Hence S is a relatively closed null set with empty
   interior.

2. **Set-up.** Suppose Ω \ S has two distinct components U₁, U₂. Each is
   open, and its relative boundary ∂U_i ∩ Ω lies in S. Put
   f_i = (u − M)·1_{U_i}.

3. **f_i is locally Lipschitz.** Take a ball B ⊂⊂ Ω, a ∈ U_i ∩ B and
   b ∈ B \ U_i. The segment [a, b] meets ∂U_i at a point c with u(c) = M.
   If L is a Lipschitz bound for u on B, then
   |f_i(a) − f_i(b)| = |u(a) − u(c)| ≤ L|a − b|.

4. **f_i ∈ H¹(Ω).** By step 3, f_i has distributional gradient
   1_{U_i}∇u (S is null). This gradient is in L²(Ω), and f_i ∈ L²(Ω).
   Hence f_i ∈ H¹(Ω), and f_i is a valid test function.

5. **Each f_i has Rayleigh quotient below μ.** Testing the weak equation
   with φ = f_i gives D_i := ∫_{U_i}|∇u|² = μ∫_{U_i}u(u − M). With
   N_i := ∫f_i² = ∫_{U_i}(u − M)²,
   μN_i − D_i = μ∫_{U_i}(u − M)(u − M − u) = μM∫_{U_i}(M − u) > 0.
   The inequality is strict because u < M a.e. on U_i. Also
   ∫f_i = −∫_{U_i}(M − u) < 0.

6. **A mean-zero combination contradicts minimality.** Choose a = −∫f₂
   and b = ∫f₁. Then w = a f₁ + b f₂ ≠ 0 has mean zero. Because the
   supports are disjoint,
   ∫|∇w|²/∫w² = (a²D₁ + b²D₂)/(a²N₁ + b²N₂) < μ.
   This contradicts the definition of μ. ∎

*Validation.* The proof uses only the weak Neumann equation and
minimality. It uses no regularity of ∂Ω (trace-free) and works in every
dimension.

*Novelty.* The restrict-and-compare mechanism is the classical
Courant/nodal one, but I found no statement of this exact
maximum-level-set form (see Section 2.8). I claim it as new to this
project only.

### 2.4 Lemma T (structure of an interior maximum set)

*Hypotheses.* Same as Lemma R, restricted to dimension two.

*Conclusion.* Every point of S is either an isolated point of S, which is
a strict local maximum of u, or lies on an embedded real-analytic arc
contained in S. The non-isolated part S₁ is a relatively closed embedded
1-manifold in Ω.

*Proof.*

1. **The Hessian at x ∈ S.** There ∇u = 0. The Hessian H is negative
   semidefinite with trace Δu(x) = −μM < 0.

2. **H definite.** Then x is a strict local maximum, hence isolated in S.

3. **H of rank 1.** Rotate coordinates so that H = diag(0, −μM) in
   coordinates (σ, s). Since ∂_s∂_s u(x) ≠ 0, the implicit function
   theorem makes {∂_s u = 0} an analytic graph s = φ(σ) near x. This graph
   contains S near x, because ∇u = 0 on S. The analytic function
   g(σ) = u(σ, φ(σ)) satisfies g ≤ M and g(0) = M. Either g ≡ M near 0, so
   S is locally that arc, or g < M for small σ ≠ 0, so x is isolated.

4. **S₁ is closed.** Limits of non-isolated points are not isolated, so S₁
   is relatively closed. ∎

### 2.5 Lemma A (spectral approximation of Lipschitz domains)

*Hypotheses.* Let Ω be a bounded simply connected planar Lipschitz domain.

*Conclusion.* There are bounded simply connected C^∞ domains Ω_k ⊂ Ω with
the following properties:

- μ(Ω_k) → μ(Ω);
- every compact K ⊂ Ω lies in Ω_k for large k;
- every sequence of L²-normalized u_k ∈ E(Ω_k) has a subsequence
  converging in C^∞_loc(Ω) to some u ∈ E(Ω) with ‖u‖₂ = 1.

In particular L(Ω) ≠ {0}, and L(Ω) = E(Ω) when dim E(Ω) = 1.

*Proof.*

1. **Cited approximation.** Take Verchota's approximating C^∞ domains
   (Verchota, J. Funct. Anal. 59 (1984), appendix; see also Kenig, CBMS
   Reg. Conf. 83 (1994), Ch. 1). These are Ω_k ⊂ Ω with uniformly bounded
   Lipschitz character and homeomorphisms Λ_k : ∂Ω → ∂Ω_k satisfying
   sup|Λ_k − id| → 0.

2. **Simple connectivity of Ω_k.** ∂Ω is a Lipschitz Jordan curve,
   because a bounded simply connected planar domain has connected
   boundary. Hence each ∂Ω_k is a Jordan curve, and Ω_k is its interior,
   so Ω_k is simply connected.

3. **Exhaustion.**
   - Fix a point x* and let K ⊂ Ω be compact. Enlarge K to a connected
     compact K' ⊂ Ω containing x*.
   - For large k, ∂Ω_k lies in a neighborhood of ∂Ω that misses K', and
     x* ∈ Ω_k. Since K' is connected and misses ∂Ω_k, it lies in Ω_k.
   - Also |Ω \ Ω_k| → 0, since Ω \ Ω_k lies in shrinking neighborhoods of
     the null set ∂Ω.

4. **Uniform extension.** Stein's extension operators (Singular
   Integrals, Ch. VI §3) give extensions E_k : H¹(Ω_k) → H¹(ℝ²) with
   uniformly bounded norms, because their norms depend only on the
   Lipschitz character.

5. **Upper bound.** Take φ ∈ E(Ω) with ‖φ‖₂ = 1 and test μ(Ω_k) with
   φ − avg_{Ω_k}φ. Its energy is at most μ(Ω). Its squared norm tends to
   1, since ∫_{Ω_k}φ → 0 and |Ω_k| → |Ω|. Hence limsup μ(Ω_k) ≤ μ(Ω).

6. **Lower bound and convergence.**
   - Normalize u_k ∈ E(Ω_k) in L². Then v_k = E_k u_k is bounded in
     H¹(ℝ²), and on a fixed ball a subsequence converges strongly in L²
     and weakly in H¹.
   - No mass is lost at the boundary: ∫_{Ω\Ω_k}v_k² ≤
     |Ω\Ω_k|^{1/2}‖v_k‖₄² → 0 (Sobolev embedding H¹ ⊂ L⁴). So the limit
     v satisfies ∫_Ω v² = 1, and similarly ∫_Ω v = 0.
   - Energy lower semicontinuity: for fixed compact K'_m ⊂ Ω_k (k large),
     ∫_{K'_m}|∇v|² ≤ liminf μ(Ω_k). Exhausting gives
     ∫_Ω|∇v|² ≤ liminf μ(Ω_k).
   - Hence μ(Ω) ≤ ∫|∇v|² ≤ liminf ≤ limsup ≤ μ(Ω). So μ(Ω_k) → μ(Ω) and
     v ∈ E(Ω).

7. **Smooth local convergence.** Interior elliptic estimates for
   (Δ + μ(Ω_k))u_k = 0 with ‖u_k‖₂ = 1 give C^j bounds on each compact
   set. Arzelà–Ascoli and a diagonal argument give C^∞_loc convergence to
   v.

8. **Simple eigenvalue.** If dim E = 1, every u ∈ E is a limit of ±c u_k.
   ∎

*Validation note.* Steps 1 and 4 are cited classical facts about
Lipschitz domains; I did not re-derive them. Steps 5–8 are proved here.

### 2.6 Theorem H (proved under the corpus premise)

*Hypotheses.* Let Ω ⊂ ℝ² be a bounded simply connected domain and
0 ≠ u ∈ L(Ω).

*Conclusions.*

- (a) u has no strict local maximum or minimum in Ω.
- (b) u attains neither sup_Ω u nor inf_Ω u at any point of Ω.
- (c) Every critical point of u in Ω is degenerate (det D²u = 0). Every
  isolated critical point has index 0.

*Consequences.* Suppose further that Ω is Lipschitz. Then:

- (d) If μ(Ω) is simple, (a)–(c) hold for every nonzero eigenfunction.
  Since Neumann eigenfunctions of Lipschitz domains are continuous on
  Ω̄ (e.g. Nittka, J. Differential Equations 251 (2011)),
  min_{∂Ω}u < u(x) < max_{∂Ω}u for all x ∈ Ω.
- (e) For every bounded simply connected Lipschitz Ω, whatever the
  multiplicity, some nonzero u ∈ E(Ω) satisfies (a)–(c) and the strict
  boundary inequalities.

*Proof.* Take Ω_k and u_k as in the definition of L(Ω). By the corpus
theorem, ∇u_k ≠ 0 in Ω_k.

- (a) Suppose x₀ is a strict local maximum. Choose B̄ = B̄(x₀, r) ⊂ Ω with
  u < u(x₀) on B̄ \ {x₀}, and put m = max_{∂B}u < u(x₀). For large k,
  B̄ ⊂ Ω_k and sup_{B̄}|u_k − u| < (u(x₀) − m)/3. Then
  u_k(x₀) > max_{∂B}u_k, so u_k has an interior maximum in B, hence a
  critical point. This contradicts the corpus theorem. Minima follow by
  replacing u with −u, which is also in L(Ω).

- (b) Suppose sup_Ω u = M is attained.
  - By Lemma T, S is the union of isolated points and S₁. Isolated points
    are strict local maxima, excluded by (a). So S₁ ≠ ∅.
  - Let C be a component of S₁. It is a closed, connected, embedded
    1-manifold, hence a properly embedded circle or line in Ω.
  - Ω is homeomorphic to ℝ² (Riemann mapping theorem). If C is a circle,
    it is a Jordan curve. If C is a line, then C ∪ {∞} is a Jordan curve
    in Ω ∪ {∞} ≅ S² (a continuous bijection from a circle).
  - By the Jordan curve theorem, Ω \ C has two components W₁, W₂. Each
    W_j \ S ≠ ∅, since S is null, and points of W₁ \ S and W₂ \ S cannot
    be joined in Ω \ S ⊂ Ω \ C. So Ω \ S is disconnected, which
    contradicts Lemma R.
  - For the infimum, apply the same argument to −u.

- (c) Suppose ∇u has an isolated zero x₀ of index ι ≠ 0 on a disk B
  containing no other zero. C¹ convergence gives ∇u_k → ∇u uniformly on
  B̄. So deg(∇u_k, B, 0) = ι ≠ 0 for large k, and ∇u_k vanishes in B,
  which is a contradiction. A nondegenerate critical point is isolated
  with index ±1, so it cannot occur.

- (d) and (e) follow from Lemma A together with (b), and continuity on Ω̄
  for the boundary inequalities. ∎

*Exact dependencies.*

- Corpus: family 369 `thm:main`.
- Classical, cited: Verchota/Kenig approximation, Stein extension,
  Lipschitz boundary continuity (only for the boundary-inequality
  phrasing in (d) and (e)), Jordan curve theorem, Riemann mapping theorem.
- Proved here: Lemmas R, T and A (steps 5–8).

*Scope.* Covered domains include all simply connected polygons and all
bounded convex planar domains, both under simple μ (case (d)), and every
such domain in the "one favorable eigenfunction" formulation of
Bañuelos–Burdzy (case (e)).

*Distinction from upstream.* Upstream proves the smooth case and full
gradient nonvanishing. Here (b) is the full strict conjecture statement.
(c) is weaker than nonvanishing: degenerate index-0 critical points, or
curves of critical points away from the extremal levels, are not excluded.

### 2.7 Precise remaining gap: accidental double eigenvalues

By Nadirashvili's bound, which upstream reproves as `prop:multiplicity`
for smooth domains, multiplicity is at most 2 in the smooth case. When
dim E(Ω) = 2, Lemma A only shows that L(Ω) contains a line. Theorem H for
*all* of E(Ω) reduces exactly to the following:

> **Gap G.** Every line in a double first-positive eigenspace is the
> locally uniform limit of first-positive eigenlines of smooth simply
> connected domains exhausting Ω.

**Attempted closures.**

1. *Symmetry-forced multiplicity.* Suppose a finite isometry group G
   preserves Ω and acts irreducibly on E. If the approximants are
   G-invariant, then the 2-dimensional cluster space of Ω_k is isomorphic
   to E as a G-representation (projections converge), hence irreducible.
   So μ(Ω_k) itself is double with eigenspace equal to the cluster, and
   L = E. This covers regular polygons whose μ is double. **Unverified
   step:** the existence of G-equivariant Verchota approximants, which is
   plausible via a G-averaged regularized distance. Status: sketch only.

2. *First-order domain perturbation.* For Φ_ε = id + εV, the splitting of
   the cluster is governed by
   q_V(f) = ∫_Ω[div V(|∇f|² − μf²) − 2∇f·DV∇f] on E. This quadratic form
   is well defined for Lipschitz Ω, with no traces. If V ↦ traceless part
   of q_V is onto Sym₀(E) ≅ ℝ², every line is reachable, and Gap G holds
   after a diagonal argument (Kato–Rellich).
   - *Obstruction:* surjectivity fails exactly when some orthonormal basis
     (f₁, f₂) of E has the traceless "stress" difference
     T(f₁) − T(f₂), with T(f) = (|∇f|² − μf²)I − 2∇f⊗∇f, having
     vanishing weak normal trace on ∂Ω.
   - For C^∞ boundary this means
     |∂_τf₁|² − μf₁² ≡ |∂_τf₂|² − μf₂² on ∂Ω.
   - I could not exclude this boundary identity in general. For the disk
     it fails (it would force μ² = 1), so the disk is nondegenerate.
   - Status: conditional reduction; the degenerate case is open.

**Not closed.** The general multiplicity-2 Lipschitz case and nonsmooth
non-Lipschitz domains are open. Quasidisks look plausible via conformal
inner approximants Φ(rD) and Jones extension, but uniform extension
constants were not verified.

### 2.8 Novelty and duplicate check

- **Upstream.** Family 369 consists of one manuscript, and it is
  restricted to C^∞ boundary. I found no Lipschitz, polygon or
  approximation corollary in its sections 01–06 or its Lean statement
  (`AdmissibleDomain` requires `SmoothBoundary`).
- **Pre-corpus literature** covers only special classes: Bañuelos–Burdzy,
  JFA 1999; Jerison–Nadirashvili, JAMS 2000; Pascu 2002; Atar–Burdzy,
  JAMS 2004 (lip domains); Miyamoto 2007; Siudeja 2015; Judge–Mondal,
  Ann. Math. 2020/2022 (triangles). Rohleder's 2024 review
  ([arXiv:2404.01890](https://arxiv.org/abs/2404.01890)) says the general
  simply connected planar case is open.
- **Searches.** Two web searches (2026-10-08) found no nonsmooth
  extension and no explicit statement of Lemma R.
- **Disposition.** Theorem H(d)/(e) is a *new-to-project* result giving a
  meaningful new case of a named conjecture, conditional only on the
  corpus. Literature priority for Lemma R is **not** established; it may
  be folklore in nodal-domain arguments.

### 2.9 Validation performed

- I re-read upstream `thm:main`, `lem:nodal`, `prop:multiplicity` and the
  conclusion proof from the pinned cache to confirm hypotheses (C^∞,
  bounded, simply connected, all of V).
- I checked every step of Lemmas R and T and Theorem H line by line,
  including:
  - the H¹ membership of f_i;
  - the strict sign μN_i − D_i = μM∫(M − u) > 0;
  - the mean-zero combination;
  - the Hessian trace −μM ≠ 0 forcing rank ≥ 1;
  - properness of line components;
  - the degree-stability argument.
- No numerical experiment was run (scipy is unavailable; numerics would
  not add proof value).
- This report has had no independent review yet.

## 3. Screened ranked targets: bridge attempts and obstructions

### 3.1 Navier–Stokes (landmark 315852)

**Corpus input.** Family 376 (six manuscripts, e.g.
`Universal-Computation-with-Eventually-Stationary-Navier-Stokes-Forcing-September-27-2026`).
For any Turing machine there is a smooth mean-zero force on 𝕋³ at fixed
computable viscosity such that a particle reaches a fixed open set iff
the machine halts. The solutions are globally smooth by construction.

**Attempt.** Clay's statements (C)/(D) allow a Schwartz/periodic force but
demand breakdown. I tried to turn "halting ⇒ entry into the detector"
into "halting ⇒ blowup" by feeding the detector into a Tao-type cascade.

**Obstruction.** Every corpus construction controls all derivatives of
the force and velocity uniformly on finite intervals. No energy-cascade
gadget is available for the true NS nonlinearity, only for averaged
models (Tao 2016, outside the corpus).

**Disposition.** Undecidability of trajectory events is proved upstream.
Blowup and regularity remain fully open. **Disproved route:** none;
**gap:** a cascade gadget.

### 3.2 Benjamini–Schramm criticality, site version (BS96 Conj. 4; not top-tier on MathDB)

**Corpus input.** Family 213.

- `No-percolation-at-criticality-on-quasi-transitive-graphs-…`, Theorem 1:
  bond percolation only.
- The cubic-lattice manuscript (site and bond on ℤ³) states verbatim:
  "The general bond criticality theorem does not imply the site
  assertion."
- Public site work cited upstream covers ℤ^d, d ≥ 3.

**Bridge attempts.**

1. Line graphs: site on L(H) equals bond on H. This is exact but trivial,
   and covers only line graphs.
2. Vertex splitting needs probability-one edges, but the theorem is for
   homogeneous p.
3. Gadget limits G_k with parallel bundles: exchanging lim_k with p_c(G_k)
   is unjustified.

**Obstruction.** The quasi-transitive proof's corridor and two-cluster
steps are written for bonds. Transferring them is a re-proof, not a
bridge.

**Disposition.** Open after the corpus, except on ℤ³, ℤ^d (public) and
line graphs.

### 3.3 Kakeya in ℝ⁵ (celebrated 315983)

**Corpus input.** `Every-four-dimensional-Kakeya-set-…/sections/10-consequences.tex`
already records dim_H ≥ 4 in ℝ^d for d ≥ 4 by projection, together with
Nikodym and Keleti–Máthé corollaries. The 3D maximal paper's
`80-consequences.tex` already gives the Nikodym and curved-Kakeya
transfers. These are duplicates and are rejected.

**Attempt.** An "(n−1)-plane brush" generalizing Wolff's hairbrush, using
full 4D dimension to beat 4 in ℝ⁵.

**Obstruction.** Tubes meeting one stem organize only into 2-planes.
Hyperplane brushes need tubes through a common 3-dimensional set, which
incidence counting does not force. The 4D input is Hausdorff, not
maximal, so it does not localize to brushes.

**Disposition.** No new bound.

### 3.4 Invariant subspace problem (celebrated 315900)

**Corpus input.** Family 293.

- `Backward-intertwiners-and-a-transitive-commutant`, Theorem 1.1: S has
  transitive commutant but explicit invariant tails L²(X; K_{≥h}).
- The companion: T_f = Uf(V) ∈ R_θ with no nontrivial invariant
  projection in R_θ.

**Attempt.** Extract a single operator with no invariant subspace from
the transitive commutant {S}'.

**Obstruction.** A transitive algebra whose members each have invariant
subspaces is consistent. Upstream explicitly warns that the
Kérchy–Pearcy claimed equivalence was withdrawn. Bishop-type weighted
rotations for Liouville angles are not touched: corpus 017 (μ(π) = 2)
concerns a non-Liouville angle that Davie already covers.

**Disposition.** Open.

### 3.5 Hilbert 16 / Smale's polynomial bound (celebrated 315873, named 405813)

**Corpus input.** `uniform-bounds-for-planar-polynomial-limit-cycles-…`,
`thm:uniform`, says B(d) < ∞, and explicitly "does not furnish an
effective formula for B(d)". The proof goes through absolute
isolated-zero finiteness and sequence-dependent flags, with no
quantitative charts.

**Disposition.** No effective bound can be extracted, so the Smale bound
B(d) ≤ d^q is open. The Liénard family (degree ≤ 5: at most 2 cycles) and
De Maesschalck–Dumortier counterexamples (degree ≥ 6) together settle
Lins Neto–de Melo–Pugh in every degree. That is a combination of known
results, not a finding.

### 3.6 Yang–Mills (landmark 315855)

**Corpus input.** Family 215: 2D O(3) massive continuum limit with mass
gap and OS axioms; exact O(4) mass asymptotics.

**Obstruction.** These are 2D σ-models with no gauge field and no
4-dimensional renormalization. There is no transfer mechanism.

**Disposition.** Open.

## 4. MathDB entries whose "open" status is superseded directly by the corpus (not findings here)

| MathDB # | Entry | Answered by |
|---|---|---|
| 389104 | Simon's "Localization in two dimensions" | Corpus 261 (uniform single-site law, all disorder) |
| 389103 | Simon's "Extended states" (d ≥ 3, weak disorder, a.c. interval) | Corpus 261 |
| 398653 | Invariant projection in W*(T) | Negative by corpus 293 companion `thm:main`, since W*(T_f) ⊆ R_θ (one-line inclusion, routine) |
| 384597, part (2) | Convex domains, n ≥ 3 | Disproved for large n by de Dios Pont 2024 (literature, not corpus) |

## 5. Status summary

| Item | Label |
|---|---|
| Lemma R (max-level non-separation, any dimension) | **proved here**; priority unknown |
| Theorem H(a)–(c) for u ∈ L(Ω) | **proved here**, conditional on corpus 369 |
| Theorem H(d): strict hot spots for simply connected Lipschitz Ω with simple μ | **proved here** (cites classical Lipschitz approximation/extension) |
| Theorem H(e): one favorable eigenfunction for every simply connected Lipschitz Ω | **proved here** |
| Double eigenvalue, general (Gap G) | **open**; conditional reduction (2.7.2); symmetric case sketched (2.7.1) |
| Site criticality, ℝ⁵ Kakeya, ISP, NS, Smale-13, YM | **open**; obstructions recorded |
| MathDB 389103, 389104, 398653 | already settled by the corpus (routine, not claimed) |

Recommended next step for the parent: send Theorem H and Lemma R to an
independent adversarial review. Focus areas:

- the cited Lipschitz approximation hypotheses (Verchota/Kenig theorem
  numbers not re-checked);
- whether Lemma R appears in Bañuelos–Burdzy or Jerison–Nadirashvili.
