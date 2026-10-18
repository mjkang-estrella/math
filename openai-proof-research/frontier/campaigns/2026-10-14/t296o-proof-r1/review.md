# T296O independent proof-correctness review, round 1

Role: proof correctness only. Contribution is a separate gate and is not judged here. This review does not accept the result; the parent alone accepts results. Source mathematics at the immutable OpenAI pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true; only the new deductions and the actual source interfaces were audited.

## Verdict

**PASS_FULL_T296O** (proof correctness of the full unchanged frozen statement).

Every frozen quantifier follows from the argument in `candidate.md` together with the stipulated source interfaces `lem:free-haar-extension`, `lem:haar-absorption` and `lem:length-one-convolution`, plus standard facts (associativity of freeness, continuous functional calculus through *-homomorphisms, the Baire category theorem for complete metric spaces). I re-derived each step below. I found **no REQUIRED objections**. The optional items at the end are presentational; none of them is needed for validity.

The verdict does not rest on a 2-norm substitute, an existential orbit statement, or any spectral restriction. Integrity checks and finite diagnostics certify no theorem.

## Authenticated input

Frozen author packet `frontier/campaigns/2026-10-14/fresh-structural-discovery-r77/`, checked against the externally supplied anchors before reading:

| file | SHA256 |
|---|---|
| MANIFEST.json | c8d45ad7426c78529c513258e28f4e5ade79b8b6b3c4795575d01647d3d569c5 |
| scope-freeze.md | 66056cf6b75951e864e69b51386d9729389f3b96f67e62b6cf5064eff9101a5b |
| candidate.md | da41f84da4934967b185ce33551dabf8b4c02ab76b711f5103fe40cded4ac857 |
| comparison.md | fe6bfb5ca0962589cb9150ef82449ea0f5ddb144e9b05e5b6204b97399f058f6 |
| reading-limits.md | 86522bd021c1c20f9e3a61cfb970b3a469fec9ea2370721e70dc4d46ba70fc50 |

`author-identity-results.json`: 25 payloads, 8 directories, exact membership, no links or nonregular entries, 9 canonical blobs matching the complete tree (SHA256 eeecc1da…5e09b, 13,223 entries, truncated=false), pinned raw URLs, the theorem labels used below present in the canonical blobs, primary receipts matching. `author-controls-results.json`: positive copied-packet acceptance and 15 reason-checked rejections. The author's own `verify.py` also passed on a /var/tmp copy and rejected a zero anchor with `MANIFEST_ANCHOR`. The author's `diagnostics.py`, run with an explicit /var/tmp output path, reproduced `diagnostics-results.json` byte for byte (2,892 checks, 3 negative controls). The frozen packet was not modified.

## Frozen statement and quantifier check

Scope (`scope-freeze.md`): for every unital irreducible inclusion P⊂M of complex II1 factors with M of separable predual, and every nonscalar u∈U(M), the set G(P,u)={v∈U(M): W*(P,vuv*)=M} is a dense G_delta subset of U(M) in the operator norm. Projection instance by u=2p−1.

| quantifier | where it is discharged | status |
|---|---|---|
| every irreducible II1 inclusion, M separable predual, P=M allowed | source lemmas need exactly irreducibility of P⊂M (II1 factors); L²(M) separability in §6; P=M trivial | follows |
| every nonscalar u, arbitrary spectrum (atoms, nonreal trace, no diffuseness) | β=1−\|τ(u)\|²>0 iff u nonscalar; no other property of u is used; u enters only as a unitary D-letter | follows |
| exact orbit vuv* | witness V_ℓ uses (w_ℓv0)u(w_ℓv0)*, an exact conjugate | follows |
| operator-norm density at every v0 | ‖v_ℓ−v0‖≤√2α/√ℓ at each coordinate, via (9)+clipping; contradiction at norm-continuity points | follows |
| G_delta of the entire locus in operator norm | ⋂_{j,n}{d_{ξ_j}<1/n}, each set norm-open | follows |
| nonseparable norm topology | only completeness of (U(M),‖·‖) and separability of L²(M) are used | follows |
| projection instance | W*(P,v(2p−1)v*)=W*(P,vpv*); 2p−1 nonscalar iff 0<p<1 | follows |

## Step-by-step re-derivation

Notation as in `candidate.md`. M^ω is the tracial ultrapower for a fixed free ultrafilter, with faithful trace, and Q=P^ω.

### 1. Source interfaces actually used

- `lem:free-haar-extension` (independence.tex): for a norm-separable unital C*-algebra D⊂M^ω there is a Haar t∈U(Q) free from D, with the endpoint formula (free-endpoints). Hypothesis: P⊂M irreducible II1 factors (the section's standing assumption). D0=C*(1,u,z,ξ) and each D_{j+1}=C*(D_j,t_j) are finitely generated, so they are norm separable; the source itself records successive application.
- `lem:haar-absorption`: for a,b∈U(D) and t Haar free from D, atb and t* are Haar free from D. Used for s_{j+1}=u·t_j with u∈U(D_j), for W=(g_ℓu)t_ℓ with g_ℓu∈U(D_ℓ), and for y=zW* with z∈U(D_ℓ).
- `lem:length-one-convolution` (Haagerup length one, with proof): ‖Σ b_γλ(γ)‖≤2(Σ|b_γ|²)^{1/2} over basis letters and inverses.
- The source's `prop:perturbation` and `lem:projection-continuity` are **not** imported as black boxes: the former is a 2-norm statement for a left perturbation and the latter is stated for the 2-norm topology. The candidate re-proves the needed analogues (§§3–6), and I checked those re-proofs rather than the source statements.

### 2. Prefix and free-Haar independence (candidate §3)

By successive absorption, s_{j+1} is Haar and free from D_j=C*(D0,s_1,…,s_j); y is Haar and free from D_ℓ. Associativity of freeness then gives that (D0, C*(s_1), …, C*(s_ℓ), C*(y)) is a free family of algebras with Haar generators. Hence D0 is free from C*(s_1,…,s_ℓ,y), and every nonidentity reduced word in s_1,…,s_ℓ,y has trace 0. The map s_k↦g_k=s_1⋯s_k is a Nielsen automorphism of the free group on s_1,…,s_ℓ (inverse s_1=g_1, s_k=g_{k−1}^{-1}g_k), so F0=⟨g_1,…,g_ℓ,y⟩ is free on those ℓ+1 letters, represented with the group trace, and free from D0. Also D_ℓ=C*(D0,g_1,…,g_ℓ), because t_j=u*s_{j+1}. Each g_k is itself Haar (g_k^n is cyclically reduced). The candidate states all of this; associativity is implicit (optional item O1).

### 3. Lemma 2.1 with arbitrary unitary D-coefficients

Let w=d_0γ_1d_1⋯γ_md_m with d_i∈U(D) and γ_i∈F0, and let deg(w)=γ_1⋯γ_m≠e. Expand each D-factor as τ(d)+d°. Dropping a scalar D-part concatenates group letters; adjacent group letters multiply and become scalar 1 only if their product is e, in which case the neighbouring D-factors merge and are re-expanded. Every operation preserves the ordered product of the group letters, so every resulting term still has group product deg(w)≠e. The process terminates because the number of factors strictly decreases at each merge. Final terms are alternating products of centered D-elements and nonidentity group elements, of length at least one, so their trace is 0 by freeness. A pure-D term would need group product e and cannot occur. Thus τ(w)=0, and w_i*w_j has degree deg(w_i)^{-1}deg(w_j). This gives orthogonality across distinct degrees and the bound ‖T‖_2≤(Σ_g a_g²)^{1/2} by the triangle inequality inside each degree and Pythagoras across degrees. No orthogonality inside a degree is assumed. **Correct.**

### 4. Exact ordered conjugation factorization (2)

Put X=u'u*=wuw*u*. Then u't_k=X·u t_k=X s_{k+1}, so W'=s_1Xs_2X⋯Xs_{ℓ+1}. Inductively, g_kXs_{k+1}⋯=(g_kXg_k*)g_{k+1}⋯, giving W'=(g_1Xg_1*)(g_2Xg_2*)⋯(g_ℓXg_ℓ*)W in increasing order, and g_kXg_k*=e^{iH_k}e^{−iJ_k} with H_k=g_khg_k*, J_k=g_kuhu*g_k*. **Correct**, and the order is essential: `factorization_eq2_matrices` checks (2) exactly with Cayley unitaries over Q(i) for ℓ≤4 and arbitrary w, and the reversed order fails in all 6 tested ℓ≥2 instances.

### 5. Complex trace β response (3)–(5)

- (3): for p∈U(D_ℓ), τ(ξ*pyp*W)=τ(ξ*pzW*p*W)=τ(ξ*pz)τ(p*). Center B=p*. The centered part gives τ(A W* B° W)=0 by the endpoint formula for W over D_ℓ, and the scalar part gives τ(B)τ(A).
- (4): τ(ξ*py*p*W)=τ(ξ*pWz*p*W)=0. The centered part of z*p* vanishes by the endpoint formula, and the scalar part is a multiple of τ(ξ*pW²)=0.
- τ(ξ*W)=0.
- p_{kj}=g_kg_j*: τ(p_{kj}*)=δ_{kj}, contributing cℓτ(ξ*z).
- q_{kj}=g_kug_j*: τ(q_{kj}*)=τ(u*g_k*g_j). This is 0 for k≠j (D0 free from a nonidentity group word) and conj(τ(u)) for k=j. Also τ(ξ*q_{kk}z)=τ(zξ*·g_k·u·g_k*)=τ(zξ*)τ(u), using g_k Haar and free from D0.
- The y*-terms vanish by (4). The q-half contributes −cℓ|τ(u)|²τ(ξ*z). Hence τ(ξ*(1+C1)W)=cℓβτ(ξ*z)=(αβ/2)τ(ξ*z). The modulus |τ(u)|² arises as τ(u)·conj(τ(u)), so the formula is right for nonreal τ(u).

**Correct.** `first_order` checks (3), (4) and (5) exactly in L(K*F) with the honest y=zW*, for 7 spectral laws (Z2, Z2², Z2³, nonabelian S3; atoms; nonreal traces; a scalar endpoint with β=0) and ℓ≤4. The wrong variants 1−τ(u)² and "omit the right conjugation factor" are both detected.

### 6. Subgroup free letters with repeated identity label

Y_p=pyp^{-1} for p∈G=⟨g_1,…,g_ℓ⟩. A reduced word in Y's with distinct successive labels expands to p_1y^{a_1}(p_1^{-1}p_2)y^{a_2}⋯y^{a_r}p_r^{-1}, which is a reduced nonidentity element of G*⟨y⟩. So {Y_p} is a free basis of the subgroup it generates. The restriction of λ_{F0} to a subgroup H decomposes over the right cosets Hx into copies of λ_H, so norms agree and (1) applies. For k≠j, p_{kj}=g_kg_j^{-1} is a reduced length-2 word determining (k,j). The identity label occurs exactly ℓ times (k=j), so Σn_p²=2ℓ²−ℓ. Then ‖λ(A)‖≤2(2c²Σn_p²)^{1/2}=2α(1−1/(2ℓ))^{1/2}. **Correct**, and this is the same A and S as the source, now realised inside F0.

### 7. Coefficientwise doubled-row envelope, including collisions

Define the envelope on formal word sums, before any identification in M^ω. It assigns to each degree g∈F0 the sum of |coefficients| of formal words of degree g. Formal concatenation multiplies degrees, so env(ST)=env(S)·env(T) in the nonnegative group ring, exactly at the formal level. Merging equal formal words, and every free reduction or collision in F0, only decreases this or leaves it unchanged. Both rows iH_k and −iJ_k have envelope exactly A_k, since deg(q_{kj}y^{±1}q_{kj}*)=Y_{p_{kj}}^{±1}. The degree-d term of the ordered product of the 2ℓ exponentials is Σ_{m_1+…+m_{2ℓ}=d} ∏_r R_r^{m_r}/m_r!. Its envelope is at most Σ ∏_r A_{k(r)}^{m_r}/m_r!, which is at most (A_1+A_1+⋯+A_ℓ+A_ℓ)^d=(2A)^d coefficientwise: each tuple is one nondecreasing row sequence of the noncommutative expansion, with weight ≤1, and all other summands are nonnegative. No commutation is used. **Correct.** Doubling is necessary. At degree y² the envelope of C_2 is C(2ℓ,2)+ℓ=2ℓ²>ℓ²=A²(y²), and `remainder_envelope` confirms both values exactly and finds single-row violations in every case (259 in total).

### 8. Convergence of every nonlinear degree; (7), (8)

‖R_r‖≤‖h‖≤α, so for fixed ℓ the sum of the term norms is at most e^{2ℓα} and degree grouping is legitimate in operator norm, hence in L². Lemma 2.1 gives ‖C_d‖_2≤‖(2A)^d‖_{ℓ²}=‖λ(2A)^dδ_e‖≤(4α)^d. The bound is uniform in ℓ and requires α<1/4. Summing over d≥2 gives 16α²/(1−4α), and Cauchy–Schwarz with ‖W‖_2=1 gives (8). **Correct.** `remainder_envelope` verifies the chain ‖C_d‖_2²≤‖env‖²≤‖(2A)^d‖²≤(Haagerup bound)^{2d} exactly for (ℓ,d)∈{(1,2),(1,3),(2,2),(2,3),(3,2)}, including nonabelian K=S3.

### 9. Actual norm estimate and clipping in the tracial ultrapower (9), (10)

h=(α/(2iℓ))Σ_j(Y_{g_j^{-1}}−Y_{g_j^{-1}}^{-1}) with distinct labels, so (1) gives ‖λ(h)‖≤2(2ℓ·α²/(4ℓ²))^{1/2}=√2α/√ℓ. The norm in M^ω equals the reduced norm: the moments τ(h^{2m}) coincide because both traces vanish on nonidentity group elements, and ‖h‖=lim τ(h^{2m})^{1/2m} for a faithful trace. Clipping is sound. The quotient ℓ^∞(ℕ,M)→M^ω is a *-homomorphism, so it commutes with continuous functional calculus: [f_ℓ(h_n)]=f_ℓ(h)=h, since spec(h)⊂[−B_ℓ,B_ℓ]. Then [w_n]=w, [u_n']=u' and [W_n']=W'. Every coordinate satisfies ‖k_n‖≤B_ℓ and ‖w_n−1‖≤B_ℓ, by |e^{it}−1|≤|t|. No norm bound on the representatives t_{j,n} or h_n beyond ‖h_n‖≤α is needed. **Correct.**

### 10. Coordinate selection (11)

{n: |τ(ξ*W_n')−τ(ξ*W')|<η}∈ω is nonempty, and the norm bound holds at every n. The chosen t_{j,n}∈U(P) are unitary representatives, as in the source's polar-decomposition lift. (11) follows with α<1/4. **Correct.**

### 11. Norm-complete nonseparable Baire space and continuity points

U(M) is norm-closed in M, hence complete; Baire needs no separability. For fixed b∈P_P, v↦b(vuv*) is norm-continuous, hence L²-continuous, and Kaplansky density gives d_ξ(v)=inf_b‖ξ−b(vuv*)‖_2. So d_ξ is upper semicontinuous and f_ξ is lower semicontinuous and bounded in the norm topology. The oscillation argument, Baire for 1/n, a countable dense family in the separable L²(M), and 1-Lipschitz dependence on ξ give a norm-dense G_delta set C at whose points every f_ξ is continuous. **Correct.**

### 12. Contradiction at a continuity point

Take v0∈C and suppose N_{v0}≠M. Choose z∈U(M)\N_{v0}, ξ=z−E(z), s=‖ξ‖_2>0 and τ(ξ*z)=s². With u0=v0uv0*, β is unchanged. Take α<min(1/8, βs/128); α may depend on v0, which is legitimate inside the contradiction. Then 1−4α>1/2, s·16α²/(1−4α)<32sα²<αβs²/4, and |τ(ξ*V_ℓ)|≥αβs²/8 for large ℓ. Since V_ℓ∈U(N_{v_ℓ}), f_ξ(v_ℓ)≥αβs²/8. But ‖v_ℓ−v0‖≤√2α/√ℓ→0 forces f_ξ(v_ℓ)→0. Hence N_v=M on C. **Correct.**

### 13. Entire generation locus G_delta

{v: d_{ξ_j}(v)<1/n} is norm-open by upper semicontinuity. All d_{ξ_j}(v)=0 implies d_ξ(v)=0 for all ξ, by the Lipschitz property, so L²(N_v)=L²(M) and N_v=M via E_{N_v}=e_v|_M. The converse is trivial. The locus is G_delta and contains the dense set C. **Correct.**

## REQUIRED objections

None.

## Optional items (not required for validity)

- O1. State associativity of freeness explicitly. Lemma 2.1 is applied with D=D0 and the group ⟨g_1,…,g_ℓ,y⟩, which needs joint freeness of (D0, s_1, …, s_ℓ, y). It follows from successive absorption plus associativity, but candidate §3 states only pieces of it.
- O2. In the q_{kk} computation, say that g_k is Haar (g_k^n is cyclically reduced), so the endpoint formula applies to τ(A g_k B g_k*)=τ(A)τ(B).
- O3. Lemma 2.1: say explicitly that the ordered product of group letters is invariant under each reduction step and that the reduction terminates.
- O4. Define the envelope on formal word sums and state env(ST)=env(S)env(T) formally, with merging and collisions only decreasing it. The current sentence ("all contributions … are added before estimating") is correct but informal.
- O5. §5: add one clause that the quotient map from ℓ^∞(ℕ,M) is a *-homomorphism, which is why clipping commutes with passing to M^ω. Optionally replace the moment argument by the trace-preserving isomorphism L(F)≅W*(free Haar family).
- O6. §4 says "Erase only D0-coefficients". In the remainder words the only D-letters are u^{±1}, and z appears only inside the group letter y. Saying so would remove any impression that z is erased as a coefficient.
- O7. Note that P=M is trivial, and that α is chosen after v0, z and ξ (through β and s).

## Finite diagnostics (bounded, never a substitute for proof)

`review_check.py finite` gives 1,100 exact Gaussian-rational checks in the group algebra of K*F. Here K∈{Z2, Z2², Z2³, S3} carries u, z, ξ, and F is free. Results are in `finite-results.json`:

- (3), (4) and (5) with honest y=zW*, for 7 laws and ℓ≤4;
- the Lemma 2.1 vanishing on 383 random mixed words, with 36 identity-degree words of nonzero trace showing the test is not vacuous;
- (2) on matrices;
- multiplicities for ℓ≤30, and Y_p freeness on 300 random words;
- the envelope and norm chain for 5 (ℓ,d) cases.

Six reason-checked negative controls are detected. The author's diagnostics treat y as an independent letter with z=ξ=1. These reviewer checks keep y=zW* and use nontrivial z and ξ, including a nonabelian D0. No infinite factor, ultrapower, clipping or Baire step is tested.

## Not judged here

Contribution, novelty and technical-adaptation significance (separate gate); manuscript and formal gates (not requested); the truth of the stipulated source and of Popa's and Haagerup's theorems.
