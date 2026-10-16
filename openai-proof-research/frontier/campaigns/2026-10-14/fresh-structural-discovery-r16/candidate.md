# B8C candidate: the complex projector plane has Borsuk number nine

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party rights retained privately.

**Status: FULL TWO-SIDED PROOF CANDIDATE for the frozen statement B8C
(`original-scope.md`, SHA256 133c0d45…dea838), awaiting independent review.**
No self-PASS, acceptance, count increase, manuscript or Lean claim is made.
The candidate PROVES B8C as frozen. It does NOT refute Borsuk in
dimension 8: X satisfies Borsuk's bound with equality, b(X) = 9 = 8 + 1.

## 0. Notation

- `<a,b> = a^* b` on C^3 (conjugate-linear in the first slot). Unit vectors
  u, v; `x_s(u) = |<s,u>|^2`. The point of X attached to u is `P_u = uu^*`.
- Herm_3: Hermitian 3x3 matrices, real dimension 9, Frobenius inner product
  `tr(AB)`. T = trace-one hyperplane, dimension 8. X = {P_u} ⊂ T.
- ω = e^{2πi/3}. Indices of C^3 coordinates are j = 0,1,2 (mod 3).
- X-shift and clock: (Xv)(j) = v(j−1), Z = diag(1, ω, ω^2). Both unitary.

## 1. Geometry

**Lemma 1.** ‖P_u − P_v‖_F^2 = 2 − 2|<u,v>|^2. Hence diam X = √2, and
two points of X are at distance √2 iff u ⟂ v. The map [u] ↦ P_u is a
homeomorphism CP^2 → X.

*Proof.* tr(P_u^2) = 1 and tr(P_uP_v) = |<u,v>|^2. Orthogonal pairs exist
(e_0, e_1). The map is continuous and injective (the range of P_u is
the line [u]) from a compact space to a Hausdorff one. ∎

**Lemma 2 (Bessel cap).** If s, u, v are unit vectors with u ⟂ v, then
x_s(u) + x_s(v) ≤ 1. So a set of unit vectors on which x_s > 1/2
contains no orthogonal pair.

## 2. Lower bound: every cover by at most eight sets fails (part 2)

This is the Hermitian analogue of the source's `lem:cover-to-map`,
`lem:positive-extension`, `lem:signed-extension` and the Borsuk–Ulam step
of prop `thm:label-bound`. The source's statements are about real
symmetric matrices and are not invoked. Every step is re-proved here.
Only continuity is used, never smoothness.

**Lemma 3 (strict-gap reduction).** Suppose X = A_1 ∪ … ∪ A_m with
diam A_i < √2 for every i (empty sets allowed). Then there are continuous
f_1, …, f_m : CP^2 → [0,1] with Σ f_i = 1 such that, for each i, the set
{f_i > 0} contains no orthogonal pair.

*Proof.* For nonempty A_i put ε_i = (√2 − diam A_i)/4. Let U_i be the
open ε_i-neighbourhood of A_i in X, and U_i = ∅ if A_i = ∅. The U_i
cover X. By the triangle inequality, diam U_i ≤ diam A_i + 2ε_i < √2. So
U_i ≠ X, and by Lemma 1, U_i contains no pair at distance √2, that is,
no orthogonal pair. Put g_i(P) = dist(P, X∖U_i). This is continuous,
and positive exactly on U_i. Σ_j g_j > 0 everywhere because the U_j
cover. Then f_i = g_i/Σ_j g_j, pulled back to CP^2 by Lemma 1. ∎

For such f, write S(u) = {i : f_i([u]) > 0}. Then u ⟂ v ⇒ S(u) ∩ S(v) = ∅.

**Lemma 4 (positive extension).** Let μ be the unitarily invariant
probability on the unit sphere S(C^3). Put H(v) = ‖v‖^2 f([v]) for v ≠ 0
and H(0) = 0. For Q ⪰ 0 define

    E(Q) = 3 ∫ H(Q^{1/2} u) dμ(u)  ∈ R^m.

Then E is continuous on the PSD cone, E(Q) ≥ 0 coordinatewise,
Σ_i E_i(Q) = tr Q, and {i : E_i(Q) > 0} = ∪_{[w] ⊂ ran Q} S(w).

*Proof.* Q ↦ Q^{1/2} is continuous on the PSD cone. H is continuous on
C^3: off 0 this is clear, and at 0 it holds because ‖H(v)‖_1 = ‖v‖^2.
So the integrand is jointly continuous on (PSD cone) × (compact sphere),
and E is continuous. Positivity is clear. Σ_i H_i(v) = ‖v‖^2 and
∫ uu^* dμ = I/3 (unitary invariance) give Σ_i E_i(Q) = 3∫<u,Qu> dμ = tr Q.

Support: every nonzero Q^{1/2}u lies in ran Q. Conversely, every line of
ran Q is spanned by some Q^{1/2}u with u a unit vector, since Q^{1/2} is
invertible on ran Q. If f_i > 0 on such a line, the i-th integrand is
positive at u, hence on an open set of positive μ-measure. ∎

**Lemma 5 (odd sphere map).** For A ∈ Herm_3 let A_± = (|A| ± A)/2 and
F(A) = E(A_+) − E(A_−). Then F is continuous and odd. If A ≠ 0 then
‖F(A)‖_1 = tr|A| > 0.

*Proof.* A ↦ |A| = (A^2)^{1/2} is continuous, and so is F. Replacing A by
−A swaps A_+ and A_−. The ranges of A_+ and A_− are orthogonal. By
Lemma 4 and the property S(u) ∩ S(v) = ∅ for u ⟂ v, the positive
coordinates of E(A_+) and E(A_−) are disjoint. So there is no
cancellation, and ‖F(A)‖_1 = tr A_+ + tr A_− = tr|A|. ∎

**Theorem A.** If X is covered by m sets of diameter < √2, then m ≥ 9.
Equivalently, part 2 of B8C holds: in every family of at most eight
subsets with union X, some member has diameter √2 (≥ √2, and ≤ √2 always).

*Proof.* Take f from Lemma 3 and F from Lemma 5. F/‖F‖_2 is a continuous
odd map from the unit sphere of Herm_3, which is S^8, to S^{m−1}. By the
Borsuk–Ulam theorem no such map exists when m − 1 < 8. ∎

## 3. The Hesse SIC and its twelve holes

Put s_0 = (0, 1, −1)/√2 and s_{a,b} = X^a Z^b s_0 (a, b ∈ Z/3). Explicitly,

    s_{0,b} = (0, ω^b, −ω^{2b})/√2,  s_{1,b} = (−ω^{2b}, 0, ω^b)/√2,
    s_{2,b} = (ω^b, −ω^{2b}, 0)/√2.

The nine *holes* are grouped into four orthonormal *bases*: the standard
basis E = (e_0, e_1, e_2) and B_c = (v_{c,0}, v_{c,1}, v_{c,2}) for
c = 0, 1, 2, where v_{c,a}(j) = ω^{c j^2 + a j}/√3. That is twelve holes
in total, and they are the four mutually unbiased bases of C^3.

**Lemma 6 (action).** Up to unimodular phases, Z e_j = e_j, X e_j = e_{j+1},
Z v_{c,a} = v_{c,a+1}, X v_{c,a} = v_{c,a+c}. So Z and X map each basis
to itself by an index shift. The nine s_{a,b} are permuted by Z and X
(up to phases).

*Proof.* (Z v_{c,a})(j) = ω^j ω^{cj^2+aj}. Also
(X v_{c,a})(j) = ω^{c(j−1)^2 + a(j−1)} = ω^{c−a} ω^{cj^2+(a−2c)j}, and
−2c ≡ c mod 3. The SIC claim follows from the relations ZX = ωXZ and
X^3 = Z^3 = I. ∎

**Lemma 7 (overlaps).** (a) |<s,s'>|^2 = 1/4 for distinct SIC vectors.
(b) For every hole h, the nine numbers x_s(h) consist of three 0s and
six 1/2s.

*Proof.* (a) A direct check on the 36 pairs. By WH covariance it suffices
to check <s_0, s_{a,b}> for (a,b) ≠ (0,0). The inner product is
(ω^b + ω^{2b})/2 = −1/2 when a = 0 and b ≠ 0. When a = 1 or 2,
exactly one coordinate product survives, giving modulus 1/2.

(b) By Lemma 6 it suffices to treat e_0 and v_{c,0}. For e_0, the values
are x = 0 for s_{0,b} and x = 1/2 for s_{1,b} and s_{2,b}. For
v_{c,0} = (1, ω^c, ω^c)/√3, the three groups give |1 − ω^{−b}|^2/6,
|1 − ω^{c+b}|^2/6 and |1 − ω^{c−b}|^2/6. These equal 0 for exactly one b
in each group and 3/6 = 1/2 otherwise, because |1 − ζ|^2 = 3 for a
primitive cube root ζ. ∎

**Lemma 8 (incidence).** Let (b_0, b_1, b_2) be one of the four bases,
with indices mod 3, and let T_b = {SIC vectors s : s ⟂ b}.
(a) T_{b_0}, T_{b_1}, T_{b_2} are disjoint triples that partition the SIC.
(b) Each s ∈ T_{b_a} lies in span(b_{a+1}, b_{a+2}), with
x_s(b_{a+1}) = x_s(b_{a+2}) = 1/2.
(c) For p, q orthonormal holes and T = T_r ⊂ span(p, q), where r is the
third basis vector, choose the phase of each s ∈ T so that <p,s> = 1/√2.
Then s = (p + γ̄_s q)/√2 with |γ_s| = 1, and the three γ_s form
γ·{1, ω, ω^2} for some unit γ.
(d) Each SIC vector is orthogonal to exactly one vector of each basis.
So each SIC vector lies on exactly four of the twelve *Hesse lines*
L(b) := b^⊥, and each line L(b) contains exactly the trio T_b.

*Proof.* (a) If s ⟂ b and s ⟂ b' with b ≠ b', then s ∝ b'' and
x_s(b'') = 1, contradicting Lemma 7(b). Each b has three orthogonal SIC
vectors, so 3 + 3 + 3 = 9.
(b) s ⟂ b_a gives s ∈ span(b_{a+1}, b_{a+2}), and then
x_s(b_{a+1}) + x_s(b_{a+2}) = 1. Neither value is 0, by disjointness, so
both are 1/2 by Lemma 7(b).
(c) |<q,s>| = 1/√2, so write <q,s> = γ̄_s/√2. For s ≠ s' in T, Lemma 7(a)
gives 1/4 = |<s,s'>|^2 = |1 + γ_s γ̄_{s'}|^2/4, so Re(γ_s γ̄_{s'}) = −1/2.
Three unit numbers with pairwise angles of 120° form a rotated set of
cube roots.
(d) Follows from (a) and Lemma 7(b). ∎

**Lemma 9 (the Hesse SIC covers with value exactly 1/2).** Put
M_0(u) = max_s x_s(u). Then M_0 ≥ 1/2 on the unit sphere, with equality
iff [u] is one of the twelve holes.

*Proof.* Write p_j = |u_j|^2. The three SIC vectors with a = 0 give
x = |u_1 − ζ u_2|^2/2 for ζ ranging over the cube roots of unity, and
similarly for the coordinate pairs (2,0) and (0,1). For a pair (a,b),

    max_ζ |u_a − ζ u_b|^2 = p_a + p_b + 2|u_a u_b| μ_{ab},
    μ_{ab} = max_ζ (−cos(arg ζ + θ_{ab})) ∈ [1/2, 1],

because among three angles 120° apart, one lies within 60° of π. Hence
M_0 ≥ (1 − p_c + √(p_a p_b))/2 for each labelling {a,b,c} = {0,1,2}.
Take c with p_c minimal. Then √(p_a p_b) ≥ p_c, so M_0 ≥ 1/2.

Equality case. Suppose M_0(u) = 1/2. With p_c minimal, √(p_a p_b) = p_c.
- If p_c = 0, then p_a p_b = 0, so u is a standard basis vector up to
  phase.
- If p_c > 0, the geometric mean equals the minimum, so p_a = p_b = p_c
  = 1/3. Then every pair group has value 1/3 + μ_{ab}/3 ≤ 1/2, so
  μ_{ab} = 1/2. That forces the three angles arg ζ + θ_{ab} to be
  {0, ±2π/3}, so ū_a u_b ∈ R_{>0}·{1, ω, ω^2} for all pairs. Fixing
  u_0 = 1/√3, we get u = (1, ω^α, ω^β)/√3, nine vectors. Since
  (c, a) ↦ (c + a, c + 2a) is a bijection of (Z/3)^2, these are exactly
  the nine v_{c,a}.

Conversely, M_0 = 1/2 at all twelve holes by Lemma 7(b). ∎

So the closed Voronoi cells of the Hesse SIC lie in closed caps
{x_s ≥ 1/2}. Each cell nevertheless contains orthogonal hole pairs on
the cap boundary (Lemma 8(b)), so its diameter is exactly √2. This is
the obstruction recorded in the scope. It is removed below.

## 4. The covariant perturbation and the nine-set cover (part 1)

**Orientation.** In each basis (b_0, b_1, b_2), say that the line L(b_a)
*favours* the pole b_{a+1}. Every hole is favoured by exactly one line.
By Lemma 6, Z and X shift indices inside each basis, so they map each
(line, favoured pole) pair to another such pair.

**Perturbation.** Put d_0 = (1 + i)(0, 1, 1)/2. Then ‖d_0‖ = 1 and
<s_0, d_0> = 0. For ε ≥ 0 put f_ε = (s_0 + ε d_0)/√(1 + ε^2), and

    s_{a,b}(ε) = X^a Z^b f_ε,   d_{a,b} = X^a Z^b d_0,
    M_ε(u) = max_{a,b} |<s_{a,b}(ε), u>|^2.

So s(ε) = (s + ε d_s)/√(1 + ε^2) with ‖d_s‖ = 1 and d_s ⟂ s, and the
configuration is the Weyl–Heisenberg orbit of the fiducial f_ε. Define
κ(s, h) = Re(<d_s, h><h, s>). This is invariant under the phase of h and
under the simultaneous phase change (s, d_s) ↦ (λs, λd_s).

**Lemma 10 (favoured pole values).** If the line L(b_a) ∋ s favours
h = b_{a+1}, then κ(s, h) ∈ {1/(2√2), 1/(2√6)}. In particular
κ(s, h) ≥ 1/√24.

*Proof.* Let W = X^a Z^b with s = W s_0, so d_s = W d_0. Then
κ(s, h) = κ(s_0, W^{−1}h), and W^{−1} maps (L(b_a), h) to a
(line, favoured pole) pair whose line contains s_0. By Lemma 7(b),
s_0 ⟂ e_0 and s_0 ⟂ v_{c,0}. So the four lines through s_0 are L(e_0),
which favours e_1, and L(v_{c,0}), which favours v_{c,1}. Computing:

- <d_0, e_1> <e_1, s_0> = ((1 − i)/2)(1/√2), with real part 1/(2√2).
- <d_0, v_{c,1}> = ((1 − i)/2) ω^c (ω + ω^2)/√3 = −(1 − i) ω^c/(2√3).
- <v_{c,1}, s_0> = ω̄^c (ω^2 − ω)/√6 = −i ω̄^c/√2.
- The product of the last two is (1 + i)/(2√6), with real part 1/(2√6).
∎

**Lemma 11 (local lemma at a hole).** Put c = 1/√12 and r = c/6 =
1/(12√3). Let h be a hole with basis labelling h = b_{a+1}, h' = b_{a+2},
h'' = b_a, so L(h'') favours h. Every unit u with <h,u> ≠ 0 is, up to
phase, u = (h + z_2 h' + z_3 h'')/N with N^2 = 1 + |z|^2. Then for
0 < ε ≤ 1/50 and |z| < r we have M_ε(u) > 1/2.

*Proof.* Let s ∈ T_{h''} or s ∈ T_{h'}. Normalise phases so that
<h,s> = 1/√2, keeping d_s attached. By Lemma 8, s = (h + γ̄ h')/√2 for
s ∈ T_{h''}. Write δ_0, δ_1, δ_2 for <d_s, h>, <d_s, h'>, <d_s, h''>, so
Σ|δ_k|^2 = 1. Put D = δ_0 + δ_1 z_2 + δ_2 z_3. Then

    <s(ε), u> = ((1 + γ z_2)/√2 + ε D) / (N √(1 + ε^2)),

and with a = |z_2|, b = |z_3|,

    2N^2(1 + ε^2)(x_{s(ε)}(u) − 1/2)
      = 2 Re(γ z_2) − b^2 + 2√2 ε Re(conj(1 + γ z_2) D) + 2ε^2|D|^2 − ε^2 N^2.

Since |z| ≤ 1, Cauchy–Schwarz gives Re D ≥ Re δ_0 − |z| and
|conj(γ z_2) D| ≤ |z|(1 + |z|) ≤ 2|z|. So
Re(conj(1 + γ z_2) D) ≥ Re δ_0 − 3|z|. Also N^2 ≤ 2. Our normalisation
gives Re δ_0 = √2 κ(s, h).

*Favoured trio T_{h''}.* Re δ_0 ≥ √2/√24 = c by Lemma 10. By
Lemma 8(c), some member has Re(γ z_2) ≥ a/2. Since 3|z| < 3r = c/2, the
right side is

    E_1 > a − b^2 + √2 c ε − 2ε^2.

*Other trio T_{h'}.* Here s = (h + γ̄' h'')/√2 and the roles of z_2 and
z_3 swap. Using only Re δ_0 ≥ −1, some member gives

    E_2 ≥ b − a^2 − 2√2(1 + c/2) ε − 2ε^2 ≥ b − a^2 − 3.25 ε − 2ε^2,

since 2√2 + √2 c < 3.237.

*Case b^2 ≤ a.* E_1 > √2 c ε − 2ε^2 = ε(0.408… − 2ε) > 0.

*Case b^2 > a.* Then a^2 < b^4 ≤ r^3 b < 10^{−3} b.
- If b ≥ 4ε: E_2 > 0.999·4ε − 3.25ε − 2ε^2 ≥ ε(0.746 − 0.04) > 0.
- If b < 4ε: E_1 > −16ε^2 + √2 c ε − 2ε^2 = ε(0.4082… − 18ε) ≥
  ε(0.4082 − 0.36) > 0.

In every case some x_{s(ε)}(u) > 1/2, because the factor 2N^2(1 + ε^2)
is positive. ∎

**Theorem B.** Let B_h = {[u] : |<h',u>|^2 + |<h'',u>|^2 < r^2 |<h,u>|^2}
be the open set |z| < r of Lemma 11, and K = CP^2 ∖ ∪_h B_h. Then
η := min_K M_0 − 1/2 > 0. For every 0 < ε ≤ min(1/50, η/3) we have
M_ε > 1/2 on all of CP^2.

*Proof.* K is compact and M_0 is continuous. M_0 > 1/2 on K by
Lemma 9, since every hole h lies in B_h. So η > 0. For unit s, s', u,

    | |<s',u>|^2 − |<s,u>|^2 | ≤ 2‖s' − s‖,

and ‖s_{a,b}(ε) − s_{a,b}‖ = ‖f_ε − s_0‖ = (2 − 2/√(1 + ε^2))^{1/2} ≤ ε.
So on K, M_ε ≥ M_0 − 2ε ≥ 1/2 + η/3 > 1/2. On each B_h, use Lemma 11. ∎

**Corollary C (part 1 of B8C).** Fix ε as in Theorem B and put

    A_{a,b} = { P_u : |<s_{a,b}(ε), u>|^2 = M_ε(u) }   (nine closed Voronoi cells).

They cover X. Each A_{a,b} is closed, hence compact, and contains no
orthogonal pair: on it the overlap with s_{a,b}(ε) is > 1/2, and
Lemma 2 applies. So the continuous distance attains its maximum on
A_{a,b} × A_{a,b} at a non-orthogonal pair, and diam A_{a,b} < √2 by
Lemma 1. Hence b(X) ≤ 9.

Equivalently, nine closed Fubini–Study balls of radius strictly less
than π/4 cover CP^2: cos^2 of the radius is 1/2 + min(M_ε − 1/2) > 1/2.

## 5. Conclusion

Theorem A and Corollary C give b(X) = 9, and diam X = √2 by Lemma 1.
That is B8C exactly as frozen: part 1 holds with actual closed sets,
and part 2 holds with no regularity assumed. In particular, the complex
projector plane is NOT a Borsuk counterexample in dimension 8. It
attains the Borsuk bound d + 1 with equality.

Relation to the source family 156. The source's lower-bound mechanism,
odd extension to all symmetric matrices plus Borsuk–Ulam, transfers to
Hermitian matrices without change and gives exactly dim Herm_3 = 9. The
source beats this count in the real case only through its ten-label
combinatorics at equality. In the complex case equality is attained:
the explicit nine-set cover shows that no analogue of the ten-label
endgame can exist for CP^2 with nine labels.

## 6. Validation performed

- `tools/diagnose_b8c.py` (pure Python, floating point, evidence only;
  run 2026-10-16). It confirmed Lemma 7(a,b), the trio sizes, d_s ⟂ s
  and ‖d_s‖ = 1, and the κ values {0.204124…, 0.353553…} =
  {1/√24, 1/(2√2)}, with minimum 1/√24 to 1e−12.
- Sampled minima of M_ε (20000 random starts, 40 descents, plus descents
  from all 12 holes): 0.500000 at ε = 0; 0.504017 at ε = 0.01;
  0.507651 at ε = 0.02; 0.517027 at ε = 0.05. Exit status 0. This agrees
  with Theorem B but is not used by any proof.
- Hand re-derivation of every constant in Lemma 11. The numerical
  inequalities used are 2√2 + √2/√12 < 3.237, √2/√12 > 0.408 and
  0.999·4 − 3.25 − 0.04 > 0.

Not done: an explicit value of η (hence of ε), an interval-arithmetic
certificate, and any independent review. None is needed for the
statement, which is existential in part 1.

## 7. Novelty limits

New to this project (no other campaign treats family 156 or the complex
projector set). Bounded literature screening found nothing settling the
Borsuk number of the complex projector set. Kalai's survey
(arXiv:1505.04952v1) treats the real x ↦ x⊗x embedding and asks for the
smallest failing dimension. "Surveying points in the complex projective
plane" (arXiv:1410.5862) classifies SICs in CP^2. It was seen only as a
search-result title and snippet, not read, and its authors were not
verified. Covering
CP^2 by nine balls of radius < π/4, and the Borsuk–Ulam lower bound, are
the kind of facts that may already be known in the quantum-design or
covering literature. No literature-novelty claim is made.

## 8. Remaining unpaid items (none blocks B8C)

1. Independent proof review of Lemmas 3–11 and Theorem B.
2. Optional: an explicit admissible ε, needing an explicit η, for a
   fully constructive cover.
