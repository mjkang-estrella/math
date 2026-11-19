# The polynomiality clause of the Nian–Tsujie–Uchiumi–Yoshinaga q-deformation conjecture fails

*Lane manuscript for MathDB 372486. Credit 0; acceptance is decided by the root. Not published. No novelty or priority claim is made here: prior-art and registry qualification are separate gates.*

## 1. Statement

Let G = ([ℓ], E) be a simple graph and F_q a finite field. The q-deformation of the graphic arrangement (NTUY arXiv:2412.08290v2, Def. 1.8; Nian arXiv:2601.06546v1, Def. 2.5) is the set of hyperplanes of F_q^ℓ

  A_G^q = { ker(Σ_{i∈C} a_i x_i) : C a clique of G, a ∈ F_q^C \ {0} }.

Def. 1.8 allows any nonzero coefficient vector on a clique. Def. 2.5 requires every coefficient on the clique to be nonzero. The two definitions give the same set, because the support of a nonzero vector on a clique is itself a nonempty clique. Coincident forms give a single hyperplane, since the arrangement is a set.

The characteristic polynomial is χ(A,t) = Σ_{X∈L(A)} μ(X) t^{dim X}, with L(A) ordered by reverse inclusion (NTUY). Equivalently, by Whitney's formula, χ(A,t) = Σ_{B⊆A} (-1)^{|B|} t^{dim ∩B} (Nian, Sec. 2).

**Conjecture** (NTUY Conj. 2.4; Nian Conj. 2.6; MathDB 372486). For every simple graph G on [ℓ]:
- (P) χ(A_G^q, t) is a polynomial in q and t; and
- (L) lim_{q→1} χ(A_G^q, q^s)/(q−1)^ℓ = χ(G, s).

The retained MathDB row writes the vertex set as `[[200~\ell]`. These are literal paste-artifact characters, with no control byte. We read them as [ℓ].

**Theorem.** There is a simple graph G on 33 vertices for which there is no Q ∈ ℂ[q, t] satisfying χ(A_G^{F_p}, t) = Q(p, t) for every prime p. In particular (P) fails, and so does the conjunction (P) ∧ (L), whatever (L) is taken to mean.

The witness lies in an explicit family of 2^26 graphs. The proof is existential and does not identify the failing member.

## 2. Reductions

For a simplicial complex Δ on a vertex set V, let S_Δ^q be the arrangement of Def. 3.1 (Nian), and define

  M_s(Δ) = #{ v ∈ (F_q^s)^V : (v_i)_{i∈C} is linearly independent for every face C }.

**(R1) Complement.** A vector v avoids every lifted hyperplane of S_Δ^q exactly when v is independent on every face. A dependence on a face C is a nonzero coefficient vector supported on C. Its support is a nonempty face, and that support gives a hyperplane of S_Δ^q containing v.

**(R2) Finite-field method.** Inclusion–exclusion over the sets of hyperplanes, together with #(W^s) = q^{s·dim W} for every subspace W, gives

  χ(S_Δ^q, q^s) = M_s(Δ)   for every s ≥ 0.

This is the identity used in NTUY Thm. 2.5. The clique complex gives the graph case A_G^q = S_{Cl(G)}^q.

**(R3) Copy-edge identity.** Let e = {i, j} be a maximal face. Then M_s(Δ∖e) − M_s(Δ) = (q−1)·M_s(Δ/e). The configurations counted on the left are exactly those where v_i is a nonzero multiple of v_j, and every other face sees i and j symmetrically. This is Nian Thm. 3.4 evaluated at t = q^s.

## 3. Theorem A: a seven-label complex

Let Δ′ be the complex on {1,…,7} whose facets are the eleven triangles

  123, 124, 134, 234, 125, 345, 136, 246, 147, 237, 567.

Put P(q) = q^6 − 4q^5 + 5q^4 + 2q^3 − 13q^2 + 10q + 1.

**Theorem A.** For every finite field F_q,

  M_3(Δ′) = (q−1)^7 q^3 (q^3−1)(q^2−1) (P(q) − [q even]).

**Proof (projective).** Every label lies in a facet, so all seven vectors are nonzero. Hence M_3 = (q−1)^7·N, where N counts 7-tuples of points of PG(2, q) with no facet triple collinear.

The four frame facets make p_1, …, p_4 a frame. The group PGL_3 acts simply transitively on ordered frames, which gives the factor |PGL_3| = q^3(q^3−1)(q^2−1). We then normalise

  p_1 = [100], p_2 = [010], p_3 = [001], p_4 = [111].

The remaining conditions are:
- p_5 lies in A_5 = PG ∖ (L_12 ∪ L_34);
- p_6 lies in A_6 = PG ∖ (L_13 ∪ L_24);
- p_7 lies in A_7 = PG ∖ (L_14 ∪ L_23);
- p_5, p_6, p_7 are not collinear.

The diagonal points are D_1 = [110], D_2 = [101] and D_3 = [011]. Their determinant is −2, so D_1, D_2, D_3 are collinear exactly in characteristic 2.

The six lines L_12, L_34, L_13, L_24, L_14, L_23 have equations z = 0, x = y, y = 0, x = z, y = z and x = 0. The basic counts are:

- |A_i| = q^2 − q.
- |A_5 ∩ A_6| = q^2 − 3q + 3. The lines L_12, L_34, L_13, L_24 meet pairwise in the six distinct points p_1, …, p_4, D_1, D_2.
- The number of ordered distinct pairs (p_5, p_6) is N_pair = (q^2−q)^2 − (q^2−3q+3) = q^4 − 2q^3 + 3q − 3.

For such a pair, let l be the line p_5p_6. If l ∉ {L_14, L_23}, then l meets L_14 ∪ L_23 in two points, or in one point when D_3 ∈ l. Both L_14 and L_23 contain D_3. Hence

  |l ∩ A_7| = (q−1) + [D_3 ∈ l] − q·[l ∈ {L_14, L_23}].

Summing over pairs gives N_frame = N_pair (q−1)^2 − N_d + q·N_line. The two correction terms are as follows.

- **N_line** counts pairs lying on L_14 or L_23. On L_14 we have L_14 ∩ A_5 = L_14 ∩ A_6 = L_14 ∖ {p_1, p_4}, and similarly on L_23. So N_line = 2(q−1)(q−2).
- **N_d** counts pairs with D_3 on their line. Note D_3 ∈ A_5 ∩ A_6. Each pair is counted on exactly one line through D_3. So N_d = Σ_{l∋D_3} |l∩A_5||l∩A_6| − (|A_5∩A_6| + q), where the subtracted term removes the diagonal pairs p_5 = p_6 (D_3 itself lies on all q+1 lines).

A line l through D_3 is neither L_12 nor L_34. So |l∩A_5| = q − 1 + [D_1 ∈ l], and likewise |l∩A_6| = q − 1 + [D_2 ∈ l]. The line sum then depends on the characteristic:

- For odd q, D_3D_1 ≠ D_3D_2. The sum is 2q(q−1) + (q−1)^3, which gives N_d = q^3 − 2q^2 + 3q − 4.
- For even q, the two lines coincide. The sum is q^2 + q(q−1)^2, which is larger by exactly (q − (q−1))^2 = 1.

Expanding,

  N_pair(q−1)^2 = q^6 − 4q^5 + 5q^4 + q^3 − 9q^2 + 9q − 3,
  q·N_line = 2q^3 − 6q^2 + 4q,

and so N_frame = P(q) − [q even]. As a check, at q = 2: A_5 = {D_2, D_3}, A_6 = {D_1, D_3} and A_7 = {D_1, D_2}, and D_1, D_2, D_3 are collinear. So N_frame(2) = 0 = P(2) − 1. ∎

**Affine form (used in the formalisation).** The Lean proof does not use projective-plane incidence facts. Linear independence of three vectors is replaced by a nonzero 3×3 determinant. An explicit equivalence then moves the facet determinants to the normalised frame. The diagonal scalings and the line scalings contribute (F^×)^3 × (F^×)^3. What remains is the set NG ⊆ F^6 of six coordinates (a, …, f) with

  a ≠ b,  c ≠ d,  e ≠ f,  det((a,b,1), (c,1,d), (1,e,f)) ≠ 0.

Its size, #NG = q^6 − 4q^5 + 5q^4 + 2q^3 − 13q^2 + 11q − κ_0, is computed with integer indicator sums. Here κ_0 = #{(b,d) : d(1−b) + b(1−d) = 0}, with κ_0 = q − 1 when 2 ≠ 0 and κ_0 = q when 2 = 0. The characteristic-2 effect enters only through κ_0, which is the affine shadow of the collinearity of D_1, D_2, D_3.

## 4. Theorem B: the graph lift

**The graph.** Take one copy vertex (f, i) for each facet f of Δ′ and each label i ∈ f, giving 33 vertices in all. The edges of G are:

- the 11 facet triangles;
- for each label, a star joining its first copy (in the facet order above) to its other copies.

Labels 1–4 have six copies each and labels 5–7 have three each. So the star edges number E_c = 4·5 + 3·2 = 26.

**The clique complex.** The facet triangles are pairwise vertex-disjoint. Two star leaves of the same label are never adjacent. So no copy edge lies in a triangle, and the cliques of G are exactly the subsets of the facet triangles together with the copy edges. The same holds for G − S with S ⊆ E_c, since removing S removes exactly the faces in S.

**The identity.** Each copy edge stays a maximal face under every sequence of identifications, because a facet carries each label at most once. Identifying along all of E_c yields Δ′. Iterating (R3), or equivalently counting the fibres of the scaling map directly, gives

  Σ_{S⊆E_c} (−1)^{26−|S|} M_s(Cl(G−S)) = (q−1)^{26} M_s(Δ′).

## 5. Conclusion: interpolation, odd primes and characteristic 2

Suppose that for every S ⊆ E_c there were Q_S ∈ ℂ[q][t] with χ(A_{G−S}^{F_p}, t) = Q_S(p, t) for all primes p. Put

  R(q) = Σ_S (−1)^{26−|S|} Q_S(q, q^3) ∈ ℂ[q].

By (R2), (R3) and Theorem A:

- for every odd prime p, R(p) = E(p), where E(q) = (q−1)^{33} q^3 (q^3−1)(q^2−1) P(q);
- R(2) = (2−1)^{26} M_3(Δ′; F_2) = 0.

There are infinitely many odd primes, so R = E as polynomials. But E(2) = 8·7·3·P(2) = 168 ≠ 0. This contradiction shows that some G − S, after relabelling to [33], violates (P), already on prime fields.

The formal statement takes Q ∈ ℂ[q][t] with arbitrary complex coefficients, and makes no degree, integrality or rationality assumption. Any reading of (P) over all prime powers implies the prime-field reading, so this proof refutes it too.

The failure is genuinely a characteristic-2 effect:
- On odd q, Theorem A is a single polynomial.
- The proof does not refute a "quasi-polynomial" reading, with one polynomial per characteristic stratum. That reading is not the native statement.

## 6. Scope of readings

These are all proved equivalent to the checked forms in the audit module.

- **Polynomial versus pointwise.** Equality in ℂ[t] after substituting q is equivalent to equality at every complex t, and also to equality at every natural t (two polynomials agreeing on ℕ coincide).
- **Möbius versus Whitney.** Defining χ through the Möbius function of L(A) (any Möbius function, or some Möbius function) gives the same (P).
- **All finite fields versus primes.** These are handled by PolyAll and PolyPrime respectively.

ℂ[q][t] is the bivariate polynomial ring ℂ[q, t]. A further reading asks only that (P) hold separately in each variable, meaning q ↦ χ(A^q, t) is polynomial on prime powers for each fixed t. This reading reduces to the joint one by Lagrange interpolation in t, because deg_t χ = ℓ. That reduction is a hand remark and is not formalised.

The limit clause (L) is not formalised. The checked conclusion holds for every predicate L, because the first conjunct fails.

## 7. Formal certificate and crosswalk

Toolchain: Lean 4.34.1 and Mathlib d13f23b7, with binaries and metadata verified against their pinned hashes. The ten modules are reproduced byte-exactly in `PAPER-APPENDIX.md`. Each module was compiled into an empty lane build and then kernel-checked separately with leanchecker. Every root uses only propext, Classical.choice and Quot.sound.

| Paper item | Lean declaration | Module |
|---|---|---|
| Def. 1.8 / 2.5 arrangement, deduplicated | `arr`, `graphArr`, `arr_eq_ntuy`, `isDeformCoeff_iff_isNTUYCoeff` | Field |
| Whitney χ | `charPoly` | Field |
| Möbius χ, Whitney = Möbius | `moebiusCharPoly`, `IsMoebius`, `charPoly_eq_moebiusCharPoly`, `isMoebius_unique` | Mobius |
| (R1)+(R2) | `avoid_iff_indep`, `indepCount_eq`, `graph_field_count_fin`, `graph_field_count_moebius` | Field, Mobius |
| (R3) | `indepCount_delete_sub`, `charPoly_delete_contract` | Deletion |
| Δ′, 11 facets | `Lift.Δ7`, `Lift.lab`, `facets_literal`, `card_facets`, `card_facet` | GraphLift, LiftFacts |
| G, E_c, cliques | `Lift.G`, `Lift.Ec`, `card_Ec`, `clique_cases`, `copyEdge_maximal` | GraphLift |
| Lift identity | `Lift.lift_identity`, `lift_identity_charPoly` | GraphLift |
| Theorem A (frame / affine) | `indepCount_Δ7_frame`, `good7_nrmT`, `N6_val`, `kap_odd`, `kap_even` | Frame, Affine |
| Theorem A (forms) | `indepCount_Δ7_all/_odd/_even/_F2/_zmod` | ProjCount |
| (P) readings | `Refute.PolyPrime`, `PolyAll`; `Audit.PolyPrimePt`, `PolyAllPt`, `PolyAllMob`, `PolyAllMobUniv` | Refute, Audit |
| §5 interpolation | `Refute.core`, `not_all_poly_Cop`, `witness33`, `witness33_all` | Refute |
| Conjunction false for every L | `ntuy_conjecture_false`, `ntuy_conjecture_false_prime`, `Audit.ntuy_false_readings` | Refute, Audit |
| §6 equivalences | `Audit.polyEq_iff_pointwise`, `polyPrimePt_iff`, `polyAllPt_iff`, `polyAllMob_iff`, `polyAllMobUniv_iff`, `witness33_readings` | Audit |

The hand proof and the formal proof divide the work as follows:
- The hand proof of Theorem A is projective. The formal proof is affine and determinant-based, so no incidence fact is assumed.
- The formal (R3) is used in its signed fibre-count form over all subsets of E_c, rather than as an iteration of single steps.
- The witness is `G.deleteEdges S` on Cop = Fin 11 × Fin 3, relabelled to Fin 33 through `finProdFinEquiv`.

## 8. Limits and remaining gates

- **No novelty claim.** No prior-art or registry clearance was done in this lane (zero GET and zero search). The earlier independent review, with a bounded 5-query search, found no prior refutation. It flagged the classical characteristic-2 (Fano) mechanism as the strongest contrary context. These remain separate gates.
- **Review not established by assembly.** This manuscript is assembled by the replay lane. An independent review of the manuscript itself is still required.
- **Definition fidelity.** The definitions are checked here against Def. 1.8, Conj. 2.4 and Thm. 2.5 (NTUY v2) and against Def. 2.5, Conj. 2.6, Def. 3.1, Conj. 3.2 and Thm. 3.4 (Nian v1). The live MathDB row was not re-read; only the retained row was used.
- **Open questions not addressed.** The failing graph is not identified, and the stratified (quasi-polynomial) reading stays open.
