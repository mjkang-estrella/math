# W012 review — Card C hyperbola hull, normal intervals and central-arc scope

2026-10-08. Independent review sub-agent, Card C focus. Scope: mathematics
and the primary source only. No candidate run, performance measurement,
parameter/depth/prime sweep, delegation, package, shared solver/Lean/STATE
edit, commit or publication. One stdlib script checks exact certificates on
two fixed semiprimes chosen in advance. It is not evidence about scaling.

**Verified factoring improvement: NONE.** Card C's mechanism is correct once
two small corrections are made. In the language of factoring it amounts to
walking the hull vertices with the 2025 paper's algorithm, which is a known
method with cost O(N^(1/3) log^2 N) arithmetic operations. The paper supplies
**no** central-arc lower or upper bound. Its "jump" primitive does **not**
certify the blocks it skips. Below I derive both central-arc bounds the paper
lacks (sections 5 and 7). They show that certifying a balanced block with no
factor costs at least about N^(1/4)/4 vertices. That is above the N^(1/5)
deterministic reference, with or without residue lattices. Every lower bound
here is a bound on vertex counts or on the size of a certificate in a named
certificate language. None is a lower bound on all algorithms.

## 0. Frozen inputs and sources

* Brief: `W012-hyperbola-hull-review-brief.txt`. Parent proposal frozen as
  `W012-hyperbola-hull-review-input-research--hypotheses--W012.md`; Card C's
  text matches the delivered brief verbatim. Project docs and the baseline
  ledger `...-input-research--hypotheses--W001-baselines.md` (the N^(1/5)
  Harvey/Harvey–Hittmeir reference) are frozen alongside it. All hashes are
  in `W012-hyperbola-hull-review-delivery-manifest.json`.
* **Primary paper:** Alcántara, Blanco, Criado and Santos (ABCS), *On the convex hull of
  integer points above the hyperbola*, arXiv:2501.19193v1, submitted 31 Jan 2025
  (only version listed). I saved the PDF, the HTML, the extracted text and the abstract page.
  I read all of sections 1, 2.1–2.4 and 3.1–3.3 in the extracted text. Theorem 1.1,
  Corollary 1.2, Theorem 2.8, Proposition 2.9 and the proof of Theorem 2.2 were also
  checked visually on rendered pages 2 and 10, because the extracted formulas are garbled.
* Sladkey, arXiv:1206.3369v1 (2012): **I read only the abstract.** It is cited here as
  prior art for geometric successive approximation under a hyperbola, used to compute
  the divisor summatory function in O(n^(1/3)) time. Its technical content was not audited.
* I did not open Khachiyan–Porkolab or arXiv:2512.19076. They belong to reviewer A or
  are out of scope.

## 1. What ABCS actually proves

| Item | Exact statement (ABCS) | Model / hypotheses |
|---|---|---|
| Thm 1.1 | 2(\|n\|/Δ)^(1/3) − 2 ≤ #vert conv(H∩Z²) ≤ C·M^(1/3)(log₂M+2), M = max{2Δ, \|n\|/Δ} | hyperbola a(x−x0)²+b(x−x0)(y−y0)+c(y−y0)² = n, Δ = √(b²−4ac) > 0, a,b,c,Δ ∈ Z, x0,y0,n real; H = closure of one convex component. C ≈ 10.81 (8.205 with optimized k) |
| Cor 1.2 | 2n^(1/3) − 2 ≤ V(n) ≤ C n^(1/3)(log₂n+2) | standard xy=n, Z² |
| Thm 2.8 / Prop 2.9 | the ⌊(n/Δ)^(1/3)⌋ lattice lines **closest to each asymptote** each carry a vertex | the source of the whole lower bound |
| Thm 2.2 (proof) | each rectangle R_i ∪ U_i holds ≤ (2⁵π²(k−1)²m/k)^(1/3) vertices; about 2·log_k m boxes | Andrews/Rabinowitz bound, κ₂ = 2π^(2/3) |
| Thm 1.3 / 1.5 | next vertex from a given vertex in O(log n), resp. O(log max{\|n\|,\|a\|,\|b\|,\|c\|}), **arithmetic operations** | RAM model: +,−,×, ⌊a/b⌋ and ⌊√a⌋ each cost O(1) |
| Cor 1.4 / 3.11 | whole hull in O(#vert · log(n+det Λ)) | Λ a **reduced** sublattice of Z² (Def. 3.1), with standard basis given |
| Prop 1.7 / Thm 3.14 | first vertex with x ≥ x_start in O(log²(n+det Λ)) operations | via Cor. 3.13, which assumes Λ reduced |
| Remark 1.6 | bit cost = arithmetic bound × M(L), where L is the input bit size and x0,y0,n ∈ Q | asserted in the paper. I did not audit the sizes of intermediate values |
| §1, §2.4 | the walk gives deterministic factoring in O(n^(1/3) log² n). The authors say it is slower than Strassen's and Bostan–Gaudry–Schost's n^(1/4+ε). Experiments for n ≤ 10⁶ "suggest" n^(1/3) log n | full hull only. The authors call the experiments inconclusive |

The paper has no theorem about the number of vertices in a clipped arc
(x in [X, √n]), about early-stopped searches, or about support queries
chosen adaptively. Section 2.4's experiments concern only the full V(n).
The jump of Thm 3.14 finds *a* vertex. It says nothing about the vertices
between the old position and the new one.

## 2. Normal-interval exclusion: exact lemmas and two corrections

Fix an affine lattice 𝓛 (either Z² or L_j). Let K = conv(H ∩ 𝓛) with
H = {x>0, y>0, xy ≥ N}. Let C(v) = [λ₋(v), λ₊(v)] be the closed set of λ > 0 for
which v minimizes λx + y over H∩𝓛. Define the tangent abscissa P_λ = √(N/λ) and
R(v) = {P_λ : λ ∈ C(v)}.

**Lemma C1 (exposure).** Suppose F = (P,Q) ∈ 𝓛 with PQ = N. Then F is the
unique minimizer of λ_F x + y over the real set H, where λ_F = N/P². By AM–GM,
λx + y ≥ λx + N/x ≥ 2√(λN), with equality only at x = P_λ and y = N/x.
So F is a vertex of K and λ_F lies in the interior of C(F).

**Lemma C2 (closed safety; correction 1).** Let v ≠ F be any vertex. Then
λ_F ∉ C(v), *including the endpoints*. Proof: the minimum over H∩𝓛 at λ_F
equals F's value, and only F attains it. If λ_F ∈ C(v), then v would also
attain it. So when v is a non-factor vertex, the **closed** abscissa range
R(v) contains no factor. The parent's warning that "endpoints need separate
treatment because an edge can tie several lattice points" is unnecessary for
the exclusion step. Lattice points in the interior of an edge are not vertices,
so by C1 they are never factors. The fixed certificates illustrate this: 17 and
145 hull edges contain interior lattice points, none of them a factor.

**Correction 2 (what a certificate needs).** Two adjacent vertices v and w
determine one supporting slope, the slope of the edge vw. That certifies a
single tangent point, not an interval. C(v) needs **both** neighbours of v.
More generally, a run of consecutive vertices v₀,…,v_k (k ≥ 2) certifies
exactly ∪_{0<i<k} C(v_i). That is the slope range from the edge v_{k−1}v_k to
the edge v₀v₁. Knowing the vertices are *consecutive* is itself the output of
`nextpt` (Thm 3.10) or of Thm 3.14's backtracking. Two vertices found by
independent jumps certify nothing between them.

**Consequence.** Over the slopes in (0,∞), the ranges R(v) are intervals that
meet only at their endpoints and together cover the whole axis. A factor is
exactly a vertex lying on the hyperbola. So "navigation by blocks of supporting
slopes" is the same thing as walking the vertex chain. Certifying a P-range
costs one `nextpt` step for every vertex whose R meets that range. The cones
give no cheaper block certificate.

## 3. Applying Theorem 1.1 to the lattice L_j of Card A (conditional on A's bijection)

I assume, as reviewer A audits, that (3) maps Z² bijectively onto L_j. Then:

* **Coefficients.** P = m·ℓ₁(i) + α and Q = m·ℓ₂(i) + β, with ℓ₁ = t₂i₁ − t₁i₂ and
  ℓ₂ = −u₂i₁ + u₁i₂. With center c defined by P(c) = Q(c) = 0, this gives
  P·Q = m²·ℓ₁ℓ₂(i−c). For a product of linear forms,
  (αδ+βγ)² − 4αβγδ = (αδ−βγ)². So the raw form has √disc = m²·|det| = m³.
  The parent's "discriminant m³, right-hand side N" is **correct for the raw form**.
* **Primitivity (exact).** Λ_j = {u ≡ r t (mod m)} with r = N j⁻² a unit. It contains
  (r,1) and (1, r⁻¹), so every basis has gcd(t₁,t₂) = gcd(u₁,u₂) = 1. Both linear
  forms are therefore primitive, and by Gauss's lemma the raw content is
  **exactly m²**. In the paper's normalization this means: primitive (a,b,c),
  **Δ = m**, **n = N/m²** (not an integer), and a rational center. The invariant
  ratio is n/Δ = N/m³, so the lower bound 2N^(1/3)/m − 2 is the same either way.
  The upper bound is not. With the raw Δ = m³, M_raw = max{2m³, N/m³}. With the
  primitive Δ = m, M = max{2m, N/m³}. Use the primitive one; the paper's proof
  itself divides out gcd(a,b,c). Certificate: N = 1022117, m = 11 gives form
  (−847, 1331, 0), content 121, M = N/1331, whereas M_raw = 2662.
* **Reducedness for §3 costs.** In (P,Q) coordinates, L_j projects onto mZ in each
  coordinate, so it is *not* reduced. Dividing both coordinates by m gives an
  index-m reduced lattice (checked), the hyperbola xy = N/m² and a rational
  offset. Thm 3.10/3.14 then cost O(log(N/m² + m)) and O(log²(N/m² + m))
  operations, after O(log m) setup (Lemma 3.2, Prop. 3.4, and two modular
  inverses for the v_i).
* **Location of the lower bound in each residue.** Push Prop. 2.9 back through the
  transformations. The N^(1/3)/m lines closest to the asymptotes are the columns
  P ≡ j (mod m) with P ≲ N^(1/3), and symmetrically the rows Q ≲ N^(1/3), which
  means P ≳ N^(2/3). **In every residue the entire full-hull lower bound lies in
  the region that small-factor trial division up to N^(1/3) removes.**

## 4. Summing over all unit residues j (mod m)

Per residue, with the primitive normalization: L_j ≥ 2(N/m³)^(1/3) − 2 and
U_j ≤ C·M^(1/3)(log₂M + 2), M = max{2m, N/m³}.

* **Regime m ≤ (N/2)^(1/4).** Σ_j U_j ≤ C·(φ(m)/m)·N^(1/3)(log₂(N/m³)+2) and
  Σ_j L_j ≥ φ(m)(2N^(1/3)/m − 2). Splitting by residue changes the total full-hull
  work by at most a factor φ(m)/m and a logarithm. The exponent stays 1/3.
  Residue hulls do not partition the vertices of the standard hull. Each factor
  pair appears in L_{P mod m} and, as (Q,P), in L_{N/j}. These coincide when
  j² ≡ N (mod m).
* **Regime m > (N/2)^(1/4)** (degenerate). Here M = 2m. The lower bound is vacuous
  once m³ ≥ N/8, and one residue hull may have O(1) vertices. But touching every
  residue costs at least φ(m) operations, and φ(m) ≫ N^(1/4)/log log N,
  which already exceeds N^(1/5).
* **Regime m ≥ √N.** For a balanced factor P < m, the residue j *is* P. Choosing
  the residue is the same as factoring.
* gcd(N,m) > 1 is handled by preprocessing. m = 1 reduces to Cor. 1.2.
* **Generation cost.** Each residue needs poly(log N) operations: the basis
  (m,0),(r,1), the v_i, normalization, a standard basis, and a first vertex or a
  jump. This is negligible except in the degenerate regime.

So summing over all residues buys nothing. A gain would require choosing
*few* residues, and that is the missing selector.

## 5. Central arc: bounds the paper does not supply (new, exact)

**Lemma C3 (abscissa width).** Let v be a vertex of conv(H∩Z²) and λ ∈ C(v).
Let P = P_λ and let x* be the integer nearest P. Then

  (v_x − P)² < (1 + η)·v_x·P²/N, where η = N/(4P²x*).

Proof: λv_x + v_y ≤ λx* + ⌈N/x*⌉ < λx* + N/x* + 1, and v_y ≥ N/v_x. With
g(x) = λx + N/x we have g(x) − g(P) = λ(x−P)²/x. So
λ(v_x−P)²/v_x < 1 + λ(x*−P)²/x* ≤ 1 + λ/(4x*). ∎

*Residue version.* On L_j, each admissible column carries Q in steps of m²
(checked: Q ≡ N P⁻¹ mod m²), and the admissible columns are spaced m apart.
The same argument gives (v_x−P)² < m²(1+η′)·v_x·P²/N, with x* ≥ P − m/2.

**Corollary C4 (central-block lower bound).** Let A = √N/2 and B = √N. Then
η ≤ 2/(√N−1). Every vertex whose R meets [A,B] has R ∩ [A,B] inside an interval
of length < 2r, where r = √((1+η)(B + √((1+η)B) + 1 + η)) = N^(1/4)(1+O(N^(−1/4))).
Hence

  #{v : R(v) ∩ [√N/2, √N] ≠ ∅} ≥ √N/(4r) = (1 − O(N^(−1/4)))·N^(1/4)/4,

and all these vertices have x in (A − r, B + r). The same argument on a dyadic
block [X, 2X] with N^(1/3) ≤ X and 2X ≤ √N gives at least
(1−o(1))·√N/(4√(2(1+η_X))·√X) vertices, about 0.158·N^(1/3) at X = N^(1/3).
So a cN^(1/3) count persists strictly to the right of the paper's lines x ≤ N^(1/3).
On L_j the central-block bound becomes (1−o(1))·N^(1/4)/(4m) per residue.
Summed over the φ(m) residues: (φ(m)/m)·N^(1/4)/4.

**Corollary C5 (window upper bound; from ABCS's own proof technique).** The
vertices with x in [x0, x0+D] lie in the box [x0, x0+D] × [N/(x0+D), N/x0 + 1),
because a vertex is the lowest lattice point of H in its column. They also lie
in the lower triangle of their bounding box. Andrews/Rabinowitz then gives
fewer than κ₂·(D(ND/(x0(x0+D)) + 1)/2)^(1/3) + 2 vertices. For the central block
this is < 2π^(2/3)((N+√N)/4)^(1/3) + 2 ≈ 2.70·N^(1/3). On L_j it becomes
< κ₂((N + m²√N)/(4m³))^(1/3) + 2. For a central window of width D the count is
O(D^(2/3)).

**Central-arc status.** The balanced block [√N/2, √N] contains between about
N^(1/4)/4 and 2.70·N^(1/3) + 2 vertices, both rigorous. The affine-length
heuristic ∫(y″)^(1/3)dx = (2N)^(1/3)·ln 2 per dyadic block suggests Θ(N^(1/3)).
Proving that would need equidistribution of {N/x} on windows of length
≈ N^(1/6) (van der Corput-type). It is not proved here, and nothing below depends on it.

**Early-stopped walks.** A walk to the right from x0 = N^(1/3) toward a factor
P ≥ 4N^(1/3) passes every vertex whose R meets [x0, P]. By C4's dyadic bound
that is Ω(N^(1/3)) vertices, whatever trial division has already done. A walk to
the left from √N to P passes at least (1−o(1))·(√N−P)/(2.3·N^(1/4)) vertices.
These count the vertices the walk itself visits. They do not bound all algorithms.

## 6. Consequences for factoring complexity

1. **No paid block skipping exists in ABCS.** Thm 3.14 locates the first vertex
   past x_start in O(log² N) operations but certifies nothing it skipped. By
   section 2, certifying a P-range needs its whole vertex chain. By C4, certifying
   the balanced block (no factor present) takes at least N^(1/4)/4 vertex steps.
   That exceeds N^(1/5) for large N, even with free jumps and free residue choice
   (summed residues: (φ(m)/m)·N^(1/4)/4).
2. **The only route below N^(1/5) is localization.** For a hull walk to use at most
   N^(1/5) vertices, it must start within a window that contains at most N^(1/5)
   vertices. By C5 a window of width D ≲ N^(3/10) suffices. By C4 a window of
   width ≲ 2.3·N^(9/20) is necessary. An N-only procedure that supplies such a
   window is exactly the missing selector. Calling it an oracle would not advance
   the construction.
3. **Comparison (pointer only; not audited in this review, not load-bearing):**
   Coppersmith/Howgrave-Graham recover a balanced P in polynomial time from an
   approximation within N^(1/4). With a window of width D they need about
   D/N^(1/4) lattice reductions, i.e. N^(1/20) at D = N^(3/10), against roughly
   D^(2/3) = N^(1/5) hull steps. Given a selector, the hull walk is therefore not
   the best way to use it. Card C's possible value lies in *producing*
   localization, not in searching a window.
4. A gcd(v_x, N) check at each vertex costs nothing extra. Vertices at multiples
   kp, k > 1, can occur (they have Lehman-type small fractional gaps), but there
   is no worst-case guarantee. It is an unexplored side remark, not a mechanism.

## 7. Cross-check on Card B's "certified gap width" (exact; complements reviewer A)

**Lemma B1.** Take any positive integers a, b, any query interval [L,U], and let
s be the exact minimum (6). The excluded integers
E = {x ∈ [L,U] ∩ Z : ax² − sx + bN < 0} are consecutive, and

  |E| < 3 + 2X^(3/2)/√N, where X = max E.

Proof: for x′ ∈ E the point (x′, ⌈N/x′⌉) is feasible, so g(x′) ∈ (s/b − 1, s/b)
with g = λx + N/x and λ = a/b. g is convex with g″ ≥ 2N/X³. Let t be the integer
minimizer and take its longer side, of length ℓ ≥ |E|/2 − 1/2. Then
g(t ± 1) ≥ g(t), so the outer derivative is ≥ 0, and the oscillation is
≥ (N/X³)(ℓ−1)², which must be < 1. ∎

*Residue version:* the candidates are spaced m apart and the feasible Q lies
within m², so the count of excluded **candidates** obeys the same bound
< 3 + 2X^(3/2)/√N.

*Implications.*
* One query excludes O(1) integers below N^(1/3) and at most about 2N^(1/4) near √N.
* A Card-B certificate that [√N/2, √N] contains no factor needs at least about
  N^(1/4)/4 queries, or (φ(m)/m)·N^(1/4)/4 over all residues.
* A certificate for [2, √N] needs Ω(N^(1/3)) queries.
* An algorithm using fewer than N^(1/5) queries clears at most O(N^(9/20))
  central integers. It can succeed only if some answer *hits* P, through the
  minimizer, a boundary root or a gcd. That again is the selector problem.
* This is a certificate-size statement. It is not a lower bound on all algorithms
  or on clever query sequences.

The parent's claim that h lies strictly inside the excluded interval held at all
five fixed query points.

## 8. Prior art

Hull enumeration as a factoring method is ABCS's own stated corollary,
O(n^(1/3) log² n) arithmetic operations. The authors compare it to Lehman's
N^(1/3) method (similar space behaviour) and rank it below Strassen's and
Bostan–Gaudry–Schost's N^(1/4+ε). The working deterministic reference is
Harvey's N^(1/5) and Harvey–Hittmeir's N^(1/5)(log N)^(16/5)/(log log N)^(3/5)
(frozen baseline ledger). Geometric approximation by lattice hulls under a
hyperbola already appears for divisor sums (Sladkey 2012, abstract only).
Nothing in Card C should be described as new machinery. The parent's text
already says this, correctly.

## 9. Scope corrections to the parent text

1. "Endpoints need separate treatment" → not needed for exclusion. The closed
   R(v) of a non-factor vertex is factor-free (C2). What needs care is
   certifying *adjacency*.
2. "Two certified adjacent vertices determine this interval" → they give one
   slope. An interval needs three consecutive vertices (correction 2).
3. "Discriminant m³, right side N" → correct for the raw form. The operative,
   primitive data are Δ = m and n = N/m² (content exactly m²). The upper-bound
   parameter is M = max{2m, N/m³}, not max{2m³, N/m³}.
4. §3 complexity statements need a reduced lattice: rescale L_j by 1/m. Costs are
   arithmetic-model counts (integer division and isqrt are unit cost), times
   M(log N) in the bit model per Remark 1.6, unaudited.
5. "≥ 2N^(1/3)/m − 2 per residue" → correct (Thm 1.1), but it lives entirely in
   P ≲ N^(1/3) or P ≳ N^(2/3).
6. The parent's MOST IMPORTANT SCOPE LIMIT is confirmed: ABCS has no central-arc,
   early-stop or adaptive-query bound. It can now be sharpened by C4/C5 (central
   block between N^(1/4)/4 and 2.70·N^(1/3)) and B1. These close *exhaustive*
   central certification as a sub-N^(1/5) route. They do not close
   selector-driven routes.

## 10. Exact certificates (fixed instances, not evidence of scaling)

`W012-hyperbola-hull-review-certificate.py`, run as `python3 -I` and writing
`...-certificate-output.json`: **50/50 checks passed.** Instances:
N = 101·103 and N = 1009·1013 (standard hulls); (N, m) = (10403, 5) and
(1022117, 11) (residue lattices); five fixed h for Card B. The checks cover:

* C1 and C2 for every factor;
* edge-interior lattice points are never factors;
* C3 at the clipped cone endpoints (largest ratio 0.946 < 1);
* central counts against C4/C5 (central-block counts 12 and 50);
* Cor. 1.2 and the Prop. 2.9 columns;
* Card A congruences (1)–(3) on these instances;
* content m², √disc m³, primitive m, Q-step m², reducedness;
* factor vertices in residue hulls, Thm 1.1 with Δ = m, and the residue C3;
* B1 with h ∈ E.

## Wave-report items

* **Best supported claim:** full or clipped hull walking factors in O(V·log N)
  arithmetic operations, where V is the number of vertices traversed. This is known
  prior art. For a balanced block with no factor, V ≥ (1−o(1))N^(1/4)/4 (new,
  rigorous) and V ≤ 2.70·N^(1/3) + 2. No assumption beyond exact integer arithmetic.
* **Verified improvement against N^(1/5): NONE.**
* **Disposition of Card C as a search engine: rejected** for exponent gains in the
  exhaustive or certifying form. **Open** only as a source of localization or
  selector information.
* **Next decisive (proof-only) step:** build an N-only procedure that narrows P to
  a window of width N^(3/10−ε) in N^(1/5−ε) paid work, or show that hull or
  support-query answers outside the window carry no such information. Separately,
  proving the Θ(N^(1/3)) central-block count is purely mathematical and would not
  change the conclusion above.
