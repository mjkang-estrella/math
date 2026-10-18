# T286F independent proof review, round 1

Verdict: **PASS_FULL_T286F**

Reviewer role: independent proof gate only (Claude Opus 5.5, Factory). This report does not judge contribution, novelty, priority, acceptance or campaign count. Count 14/20 gave no presumption. Uploads remain stopped.

Reviewed packet: `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r39/`, authenticated against the externally supplied manifest SHA256 `4d14a7c7515c455d2108f4dfc9cd64adf09539d31d57ff2bb71fb47418040af9` before any inventory was trusted (see `author-packet-checks.json`). The named files matched their dispatch hashes: candidate286f.md `1b43b798…2c`, scope286f.md `f905fbf9…98` (unchanged frozen scope), verify.py `a2ecf261…ca`, source-and-credit286f.md `de08204c…bb`.

## 1. Scope reviewed (unchanged, not weakened)

Let Γ be any countably infinite ICC group abstractly commensurable with a lattice in a finite nonempty product of noncompact property-(T) groups H_i(k_i)^+, k_i real, complex or a finite extension of Q_p (primes may differ), H_i connected adjoint absolutely simple. Let μ be any normalized T-valued 2-cocycle and M = L_μ(Γ). Then:

1. every full replete unitary fusion subcategory D of bifinite M-M correspondences (contains the unit, closed under finite sums, all subobjects, Connes fusion and conjugation, finitely many simple classes) is group-theoretical;
2. both even categories of every finite-index finite-depth inclusion P ⊂ M of II_1 factors are group-theoretical.

No irreducibility, cocompactness or torsion-freeness of the lattice, no finite-order/finite-type condition on μ, and no irreducibility of P ⊂ M is assumed. I checked the proof at exactly this scope. Nothing below uses any of the excluded hypotheses.

## 2. Exact source interfaces used (stipulated, not audited)

Read in full at the pinned commit `fd4aeeb2…eb` (blobs independently authenticated, see `author-packet-checks.json`):

- Arithmeticity companion, `build/sections/00-introduction.tex` (all 336 lines): Definition `def:class` is exactly the scope class (lines 17–35; "No irreducibility, cocompactness, product decomposition, or torsion hypothesis"); normalized cocycles (45–49); Theorem `thm:arithmetic-exhaustion` (99–118) with Λ any countably infinite ICC group and arbitrary normalized μ, ω.
- Arithmetic-category companion, `01-introduction.tex` (all 414 lines): germ action, full stabilizer C_d, joint multiplier α, H(d,σ_d) = E(A_d,B_d,δ_d,σ̃_d), Theorem `thm:correspondences` (247–277).
- Same, `02-models.tex` (all 74 lines): relative tensor convention; Proposition `prop:recovery-exhaustion` (55–64), stated for separable bifinite correspondences.
- Same, `03-calculus.tex` (all 792 lines): Lemma `lem:calculus-germ-test`, projective induction (A1), graph-bundle unitary, regrouping (eq:calculus-regrouping), representative change (eq:calculus-representative-change), Theorem `thm:calculus-hom`, the Remark identifying E(A,A,id_A,1) with the permutation representation, conjugation (eq:calculus-conjugate-transport and lines 477–479), Proposition `prop:calculus-fusion`, the double-coset fibre and q_m (eq:calculus-double-coset-fibre, -fusion), and the map/associativity/unit/conjugation compatibility (718–778).

Interface fit: Γ ∈ 𝒦, Λ = Γ (countably infinite ICC), ω = μ. Bifinite correspondences over the separable factor M are finitely generated over L²(M) and therefore separable, so the source's separability convention costs nothing.

## 3. Independent rederivation

Notation: 𝔇 = Γ×Γ, α((g,h),(g',h')) = μ(g,g')·conj μ(h,h'). By the stipulated Theorem `thm:correspondences`, every object of D is a finite orthogonal sum of full-germ bundles H(d,σ_d). By `thm:calculus-hom`, all maps are fibrewise, so a simple object is a single orbit with an irreducible fibre.

### 3.1 Identity sector and the finite quotient (candidate §1)

The identity-germ orbit is the set of inner germs. By ICC (injectivity of g ↦ [Ad g], `lem:calculus-germ-test`), C_id is the diagonal Γ. On the diagonal α = μ·conj μ = 1, so fibres are ordinary finite-dimensional unitary representations. Let D0 be the full subcategory of D supported on this orbit, and S the set of representations ρ with H(id,ρ) ∈ D.

- **Tensor.** The double-coset formula with δ = ε = id_Γ has one double coset, m = e, q_e(b) = μ(b,e)/μ(e,b) = 1. So H(id,ρ)⊗H(id,ρ') = E(Γ,Γ,id,ρ⊗ρ'). The full stabilizer is already the graph, so no regrouping is needed.
- **Conjugation.** By the conjugation rule this gives conj ρ.
- **Subobjects.** By `thm:calculus-hom`, subobjects are exactly subrepresentations.

So S is closed under ⊗, conjugation, subrepresentations and sums, contains 1, and has finitely many irreducibles ρ_1,…,ρ_n.

Coefficient argument (checked):

1. The span C of the coefficients of the ρ_i is a finite-dimensional unital commutative *-algebra of functions on Γ. Products land in C because ρ_i⊗ρ_j decomposes into the ρ_k (unitary complete reducibility). Conjugates land in C because conj ρ_i ∈ S.
2. Let K = ∩ ker ρ_i. Evaluations ev_g, ev_h are equal iff ρ_i(g) = ρ_i(h) for all i, iff gK = hK. There are at most dim C characters, so Q = Γ/K is finite and K is normal.
3. C is a unital self-adjoint subalgebra of Fun(Q) that separates points, so C = Fun(Q).
4. Schur orthogonality on Q then forces every irreducible of Q into S.

Hence S = Rep(Q) inflated to Γ, and K is the common kernel of all of S. **Correct.**

### 3.2 Exact identity summand (candidate §2)

Let X = H(d,σ) ∈ D with full graph δ = δ_d : A → B and σ̃(a) = σ(a,δa), whose multiplier is μ|_A/δ*μ.

First fusion. X⊗H(id,ρ) = E(A,B,δ,σ̃)⊗E(Γ,Γ,id,ρ). Here B\Γ/Γ is a single double coset with m = e, and:

- A_e = δ^{-1}(B∩Γ) = A
- θ_e = δ, F_e = B
- c = b = δ(a), q_e = 1
- fibre σ̃ ⊗ (ρ∘δ)

Second fusion, with X̄ = E(B,A,δ^{-1}, b ↦ conj σ̃(δ^{-1}b)). Take the identity double coset B·B in B\Γ/B (m = e):

- A_e = δ^{-1}(B∩B) = A, θ_e = δ^{-1}∘Ad(e)∘δ = id_A, F_e = A
- c = δ(a), τ(c) = conj σ̃(a), q_e = 1

The resulting fibre is

  γ(a) = σ̃(a) ⊗ ρ(δa) ⊗ conj σ̃(a),

with multiplier μ|_A/id*μ|_A = 1: the two projective multipliers β and conj β cancel. E(A,A,id_A,γ) is a closed summand of X⊗H(id,ρ)⊗X̄; the source fusion unitaries are actual bimodule unitaries, and associativity is the ordinary one.

Regrouping. Regrouping at the full stabilizer (diagonal Γ, where α|_diag = 1, so (A1) is ordinary induction) gives H(id, W_ρ) with W_ρ = Ind_A^Γ γ. By fullness and closure under subobjects, W_ρ ∈ S. Only this one summand is used. **Correct.**

### 3.3 Common kernel, scalar fibres, two-sided invariance (candidate §3)

- **K ⊂ A.** For ρ = 1, γ = σ̃⊗conj σ̃ ≅ End(V_σ) with Ad σ̃, which contains the invariant identity line. Ind_A^Γ 1 = ℓ²(Γ/A) is therefore a subrepresentation of W_1 ∈ S, and K ⊂ ker(Γ ↷ Γ/A) = core_Γ(A) ⊂ A.
- **Scalar σ̃ on K.** Since K ⊂ core(A), K fixes every coset. On the identity coset block (r_A = e, transport γ(k)), triviality of W_1 on K gives Ad σ̃(k) = id on End(V). So σ̃(k) is central in M_n(C) and unitary: σ̃(k) = c_d(k)I with c_d(k) ∈ T. Its image is not claimed finite.
- **δ(K) ⊂ K.** For every ρ ∈ S, the identity block of W_ρ at k ∈ K is c_d(k)·conj c_d(k)·ρ(δk) = ρ(δk) = I. Since K is the common kernel of S, δ(K) ⊂ K.
- **Reverse inclusion.** X̄ ∈ D is the bundle of the inverse germ, with full stabilizer C_d^op and graph δ^{-1} : B → A. The same argument gives K ⊂ B and δ^{-1}(K) ⊂ K. Hence **δ(K) = K**.

K depends only on D0. Simplicity of X is not even needed. **Correct.**

### 3.4 Restriction to N = L_{μ|K}(K) (candidate §4)

K has finite index in an ICC group, so it is ICC: a finite K-class of k ≠ e would give a finite Γ-class, as the union of finitely many conjugates of it. So N is a II_1 factor, and N ⊂ M has index q = [Γ:K].

For X = H(C_d,σ):

- The K×K orbits on 𝔇/C_d are finite in number, since K×K has finite index in 𝔇.
- For a label s·C_d with s = (g,h), the stabilizer in K×K is (K×K) ∩ sC_d s^{-1}. Because K ◁ Γ, K ⊂ A_d and δ(K) = K, this is exactly the graph of θ = Ad(h)∘δ∘Ad(g^{-1}) on all of K, and θ is an automorphism of K.
- Representative change (eq:calculus-representative-change) gives the fibre representation at the label: (k,θk) ↦ [α-scalar]·σ(s^{-1}(k,θk)s) = [scalar]·σ̃(g^{-1}kg) = scalar·I. So every line of V is invariant.
- The K×K-bundle over the orbit is the projective induction from the stabilizer of these lines. Restricting the joint unitary action U_{(k,l)} = u_k · u_l^* and using normality (Lemma `lem:calculus-induction` for (K, μ|_K)) identifies it as an N-N correspondence with a finite sum of one-dimensional graph models E_K(K,K,θ,χ).

For each such model, χ(k)χ(l)/χ(kl) = μ(k,l)/μ(θk,θl). I checked directly that α(u_k) = χ(k)u_{θ(k)} is multiplicative and is implemented by the unitary δ_k ↦ χ(k)δ_{θ(k)} on ℓ²(K):

  Wλ_μ(k)W*δ_{θ(l)} = χ(k)μ(θk,θl)δ_{θ(kl)} = α(u_k)δ_{θ(l)}.

So α is a normal, trace-preserving automorphism, and E_K(K,K,θ,χ) ≅ _αL²(N) is invertible. All cocycle phases are kept. **Correct.**

### 3.5 The regular Q-system (candidate §5)

- **A is in D.** A = L²(M)⊗_N L²(M) is literally the source model E(K,K,id_K,1). Regrouped at the diagonal it is H(id, ℓ²(Γ/K)), the left regular representation of Q, which is in S. So A ∈ D0 ⊂ D.
- **Free basis.** L²(M)_N is free with basis (u_r), r ∈ Γ/K, because E_N(u_r^*u_s) = δ_{rs}. So M1 = ⟨M,e_N⟩ ≅ M_q(N).
- **Pimsner–Popa relations.** Σ_r u_r e_N u_r^* = 1, and e_N x e_N = E_N(x)e_N.
- **Unitary U.** U(a⊗b) = √q·a e_N b is well defined (N commutes with e_N). It is isometric:

  q·tr_{M1}(b^*E_N(a^*a')e_N b') = tr(E_N(a^*a')b'b^*) = ⟨a⊗b, a'⊗b'⟩.

  It is onto because span Me_N M = M1.
- **Multiplication normalization.** I recomputed U(ζ_r) = √q·u_r e_N u_r^*, which gives U(ζ_r)U(ζ_s) = q·δ_{rs}·u_r e_N u_r^*, so ζ_rζ_s = √q·δ_{rs}ζ_r and 1 = q^{-1/2}Σζ_r ↔ 1_{M1}.
- **Γ-action.** The diagonal Γ permutes the ζ_r: scalars cancel in u_g u_r ⊗ u_r^* u_g^*, and u_k e_N u_k^* = e_N.
- **Q-system structure.** On the identity fibre the multiplication is δ_r⊗δ_s ↦ √q·δ_{rs}δ_r. So mm^* = q·id (special), ‖η‖ = 1, and A is the commutative Frobenius algebra Fun(Q).
- **Connected.** Hom(1,A) = Hom_Γ(1, ℓ²(Q)) = C (equivalently, N'∩M = C because every nontrivial K-class in Γ is infinite).
- **Maps in D.** m and η are M-M intertwiners between objects of D, so by fullness they lie in D.

**Correct.** The normalization only fixes a scale and does not affect the bimodule category.

### 3.6 Morita dual and the II_1 corner bridge (candidate §6)

Classical input (EGNO, read at text lines 8930–9175): Proposition 7.11.1, Remark 7.12.5, Definition 7.12.17 and the note after it say that D is categorically Morita equivalent to C iff C ≅ Bimod_D(A) for an exact algebra A. Proposition 7.12.18 gives transitivity. A in a fusion category with separable multiplication is exact. Connectedness makes Mod_D(A) indecomposable, so Bimod_D(A) has a simple unit. These hypotheses fit.

Operator bridge (checked in detail):

1. **(4) ⇔ normal M1-action.** I checked that relation (4) implies Pn = nP. From PxP = E_N(x)P with x = n, n^* and taking adjoints: nP = PnP = Pn.
2. **Well-defined and multiplicative.** Expanding x = Σu_rE_N(u_r^*x) and y = Σ E_N(yu_s)u_s^* reduces Σ x_iPy_i to the matrix (Σ_i E_N(u_r^*x_i)E_N(y_iu_s))_{rs}. So the map (5) is well defined on M1 = Me_N M ≅ M_q(N) and multiplicative (P u_s^*u_t P = δ_{st}P).
3. **Normality.** It is normal because the matrix units are finitely many and the N-action is normal.
4. **From an M1-action to a bounded A-action.** Conversely, a normal M1-action gives a bounded λ : L²(M1)⊗_M H → H by the Pimsner–Popa inequality E_M(y) ≥ q^{-1}y for y in M_n(M1)_+.
5. **Maps.** M-M maps commuting with both P's are exactly the A-A maps, and these are D-morphisms by fullness.
6. **Corner functor.** F(H) = eHe is an (eM1e ≅ N)-bimodule; on eHe the action of ne equals that of n. Since e = e_N is a full projection in the factor M1 ≅ M_q(N), the full corner gives an equivalence of all M1-M1 correspondences with N-N correspondences (C^q⊗Y⊗conj C^q ↔ Y). It is fully faithful, closed under subobjects and conjugates, and monoidal: He ⊗_N eH' ≅ H ⊗_{M1} H'. The unit maps as F(L²M1) = L²(N).
7. **Image is pointed.** e ∈ N'∩M1, so eHe is a closed N-N subobject of Res_N(H|_M). By §3.4 that restriction is a finite sum of invertible N-N correspondences. A simple H ∈ E has End = C, hence F(H) is irreducible, hence F(H) is invertible. Its inverse F(H̄) lies in the image. Because F is fully faithful and monoidal, H⊗_A H̄ ≅ A. So E is pointed.
8. **Conclusion.** E ≅ Vec_G^ω with ω a unitary 3-cocycle, and D is group-theoretical. **Correct.**

### 3.7 Finite-depth, possibly reducible inclusions (candidate §7)

Let P ⊂ M be finite index, finite depth, both II_1 factors, P'∩M arbitrary, ρ = _M L²(M)_P.

- **M-M side.** Let D_M be the full replete subcategory generated by the summands of (ρρ̄)^n. It contains the unit and is closed under fusion, conjugation and subobjects. Finite depth gives finitely many simples. So §§3.1–3.6 apply.
- **P-P side.** I checked independently that the P-P even part D_P is categorically Morita equivalent to D_M without connectedness:
  - A' = ρρ̄ ≅ L²(M1'), where M1' = ⟨M,e_P⟩ is a factor (M1' = JP'J).
  - e_P is a full projection with e_P M1' e_P = Pe_P, valid without irreducibility.
  - A'-bimodules in D_M are realized as M1'-M1' correspondences. The corner maps them into Res_P = ρ̄(·)ρ, which lies in D_P because ρ̄(ρρ̄)^nρ = (ρ̄ρ)^{n+1}.
  - Every Y ∈ D_P is the corner of L²(M)⊗_P Y ⊗_P L²(M).
  - So D_P ≅ Bimod_{D_M}(A'). A' is exact, and D_P has a simple unit because P is a factor. EGNO's note after Definition 7.12.17 applies.
- **Conclusion.** Group-theoreticality transfers by Proposition 7.12.18. **Correct.** See optional O4 on the presentation.

## 4. Required objections

**None.** I found no gap, counterexample, scope weakening, or illegitimate use of excluded hypotheses.

## 5. Optional objections (presentation; non-blocking)

- **O1 (§6, algebraic vs. standard modules).** EGNO's Bimod_D(A) consists of all algebraic bimodules, while E is defined with standard (unitary) ones. Add one sentence. Every algebraic A-bimodule is a summand of a free one A⊗X⊗A (separability). Free ones are standard. Idempotents in the finite-dimensional C*-algebra End_{A-A} are similar to projections, whose ranges are standard. Hence the inclusion is an equivalence. Also state explicitly that "standard" is the condition making π *-preserving.
- **O2 (§6, boundedness).** Name the bound for λ(x̂⊗ξ) = π(x)ξ: Pimsner–Popa E_M(y) ≥ q^{-1}y, amplified to matrices, gives norm ≤ √q. "Bounded because finite index" is correct but terse.
- **O3 (§6, relative tensor products).** "Relative tensor product over A is fusion over M1" deserves the explicit separability projection on H⊗_M H' (built from a Pimsner–Popa basis of M1 over M) and its image ≅ H⊗_{M1}H'. Classical, but it is the step BKLR states in type III form.
- **O4 (§7).** Izumi 2018 p474 is an informal introductory sentence, not a proof, and Izumi's later sections were not read. Replace or supplement it with the short argument in §3.7 above, or with a precise classical reference (EGNO's note after Definition 7.12.17 already needs only an exact algebra). The phrase "the inclusion supplies a nonzero bridge, so this module category is indecomposable" should be expanded: for simple Y, Y′ in the M-P category, Y′ ⊂ (Y′Ȳ)Y with Y′Ȳ ∈ D_M, because ȲY ⊇ L²(P).
- **O5 (§5 wording).** "Standard Hilbert normalization" should be stated as mm^* = q·id, η^*η = 1 (special Frobenius). This differs from BKLR's normalization by scalars, which is harmless.
- **O6 (§1).** Say explicitly that the tensor and conjugation closure of D0 comes from the m = e double-coset term with q_e = 1 and the diagonal multiplier α = 1, as in §3.1 above.

## 6. Non-claims

No contribution, literature-novelty or acceptance judgement is made. Checksums and inventory controls certify bytes only and are not mathematical evidence. No numerical computation was used or needed; the verdict rests solely on the categorical/operator argument above. Upstream source proofs (geometric exhaustion, map-level calculus) were not audited, as instructed.
