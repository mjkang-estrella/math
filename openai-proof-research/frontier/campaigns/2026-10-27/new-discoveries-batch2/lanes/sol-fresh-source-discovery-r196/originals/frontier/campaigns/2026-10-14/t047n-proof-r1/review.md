# T047N independent adversarial proof review, round 1

Verdict: **PASS_FULL_T047N.** No required mathematical objection. Nine optional presentation or verifier items follow.

Role: independent proof gate only. No contribution, novelty or substantiality verdict is given here. No source audit: theorems of the pinned repository at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true, as instructed. The parent alone decides adoption. Campaign count 13/20 (target 20) is unaffected by this review. No nested agents, staging, commits, shared-metadata edits, count changes or uploads occurred. The parallel review packet, the contribution review, `t047n-parent/` and `t047n-author-primary-clarification-r1/` were not read.

## 1. Frozen inputs and external anchors

Author directory: `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r29/`. External anchors were supplied by the parent and recomputed before reading:

| File | SHA256 (supplied = recomputed) |
|---|---|
| manifest.json | c7eec0bc68f9bb04945e92187ac772fe5339de470745cecb04744db17d1d35cd |
| verify.py | 609d25eb1ac648f93e5d430fbaf8a09daf19555c1283bb86e5f59ba94adcf880 |
| candidate-047.md | 8f68f16a99340c9cf3c83c4ae86386fdcfe2f907bf337afd7f303c7ad0910039 |
| scope-047.md | 12e3fb5941a068df0380710b8dcef236e313cdc22ed872ad372b3dab5dfcf181 |
| sources/preprints-tree.json | eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b |

`sources/tree.json` was not used. The verifier was read in full before execution; it is read-only (no writes, no network). The frozen packet was not modified (copies only for controls).

## 2. Scope coverage (frozen scope, unchanged)

The candidate's §1 theorem is exactly the frozen scope: every integer n≥2, over C, H_n, A_n, X_n as displayed; arbitrary C-variety isomorphisms with no marking. No finite-n, marked-p, conditional or weakened replacement is used.

| Scope item | Where proved | Review status |
|---|---|---|
| X_n integral, dimension 4, affine | §2 | Re-derived, correct |
| X_n smooth | §2 (descent from the cylinder) | Re-derived, correct |
| X_n×A¹≅A⁵ for all n≥2 | §2, (2.2)–(2.4) | Re-derived for symbolic n; exact identities checked n=2..7 |
| X_n≄A⁴ | §5 (DK(A_n)=S_n≠A_n) | Correct; also implied by §4 |
| DK(A_n)=S_n, both inclusions | §4 upper, §5 lower (incl. u) | Re-derived, correct |
| Recovery of pS_n via the canonical morphism, all points | §6 | Re-derived, correct |
| Reduced staircase image(J_r)=I^⌈r/n⌉ for all r≥1 | §7 | Re-derived, correct |
| Pairwise X_n≄X_m (n≠m) under arbitrary isomorphisms | §§5–7, (7.2) | Re-derived, correct |

No nonprincipal-center claim is made, and none is needed: the argument uses only I²≠I (Nakayama), which is proved. No moving-polynomial statement is asserted. The §8 Euler-characteristic remark is ancillary and unused; I checked it anyway (χ_c=0+2·1=2).

## 3. Independent re-derivation

All steps below were redone by hand before reading the author's diagnostics. The author's `diagnostic.py` was not run and is not relied on.

### 3.1 Integrality and localization (§2)

Substituting y and z gives xy−z(z+1)=x²(x−u³−s²)−p^n(1+2sx)J−p^{2n}J² = p^n(H_n+pu), using x−u³−s²=p^nF. Over C[p^{±1}], (x,y,z,u) are coordinates with the displayed inverse. H_n=p^{−n}(xy−z(z+1))−pu is a coordinate, since its u-coefficient −p is a unit, so it is prime after localization. Modulo p, H_n≡x₀²F−(1+2sx₀)J≠0 (both p^nJ² and pu vanish for n≥1). In the UFD P, any irreducible factor that becomes a unit is associate to p, which is excluded. Hence H_n is prime, A_n is a domain with fraction field C(p,x,y,z), and dim A_n=4.

### 3.2 Cylinder for every n (§2)

- Δ=−p^n∂_u in coordinates (p,x,y,z,u). From s=y−x²+xu³: Δs=−3p^nxu². Also ΔF=(−2sΔs−3u²Δu)/p^n=(6sx+3)u² and ΔJ=−xΔs/p^n=3x²u². These values lie in P, and Δ kills x, y and z (checked exactly). Since ΔH_n=−pΔu=p^{n+1} and Δ²H_n=0, we get Φ(H_n)=H_n+p^{n+1}w.
- The (F,J)→(L,M) matrix has determinant 4s²x₀²+(1−4s²x₀²)=1, and the stated inverse is correct.
- H_n(L)=L−pu+p^nQ(L)+p^{2n}F(L)³ follows from x=x₀+p^nF.
- For (2.3): H_n(L_*)=p^nL_*Q₁(L_*)+p^{2n}F(L_*)³. Factoring out p^{n+1} gives the displayed form. This is valid for every n≥1.
- For (2.4): L−ph=H_n+p^{n+1}w. Expanding both sides, they agree term by term (−p^nC−p^{n+1}Q₁h−L+pu−p^{2n}F³−p^{n+1}w).
- W(Z)∈B[Z] holds because H_n(L_*+p^{n+1}Z)−H_n(L_*) is divisible by p^{n+1}Z, and (2.3) supplies the remaining divisibility.
- T≅A[w] is a domain with p≠0, so w=W(e), T=B[e], and e is transcendental over B[p^{−1}]. Hence T≅C^{[5]}.
- Smoothness: X×A¹→X is faithfully flat and X×A¹ is regular, so X is regular, hence smooth over C. The candidate's tangent-dimension argument is equivalent.

### 3.3 Exact valuation filtration (§3)

- S→A is well defined: the S-relation maps to p^nH_n=0. It is injective because S is a domain (relation linear in u with unit coefficient after localization, and not divisible by p) and S[p^{−1}]=A[p^{−1}].
- R is a smooth domain. pS is prime, and S_(pS) is a local noetherian domain with nonzero principal maximal ideal, hence a DVR.
- (3.1): primality gives pS_(pS)∩S=pS; iterate. (3.2) follows. Therefore F₀A={a∈A: ord_p a≥0}=A∩S=S exactly.
- Initial forms: ord_p(F)=ord_p(J)=−n because f and g are nonzero in R. Check: on the closed subset x=z=0 of Spec R, f=−y²−u³; on x=0, z=−1, g=−1.
- θ: P→R[τ^{±1}] has image R[τ,f/τ^n,g/τ^n], since θ(x)=x, θ(y)=y and θ(z)=z.
- ker θ=(H_top): after inverting p, θ is the quotient by xy−z(z+1)=p^nH_top. H_top is prime in P (same UFD argument; H_top≡x₀²F−(1+2sx₀)J mod p), so (H_top) is p-saturated.
- Cancellation step: the weight-M part Q_M maps under θ to the image of the degree-M class of a. That class is zero because a∈F_{M−1}, so Q_M=H_topC with C homogeneous of weight M−n. Then Q−H_nC has maximum weight <M, because the leftover puC has weight M−n−1. Termination: weights are integers, never below deg a, and strictly decreasing. Hence gr A=θ(P)≅P/(H_top) exactly, not merely an inclusion.
- G is smooth: on τ≠0 it is R[τ^{±1}]. At p=0, ∂H_top/∂F=x₀² and ∂H_top/∂J=−(1+2sx₀) (checked exactly, including the p^n-dependence of x), and these cannot vanish together because (1−2sx₀)(1+2sx₀)+4s²x₀²=1.

### 3.4 Upper DK bound (§4)

- **Induced derivation.** The source047 induced-LND lemma uses only exact-weight representatives of the five generators, so it applies verbatim for every n. If D≠0 had an invariant outside S=F₀A, that invariant would have positive degree, and its initial form would be a nonzero positive-degree homogeneous D₀-invariant.
- **Torsor.** R, I, R~ and v are literally unchanged, so I·R~=(v) is the source's n-free certificate (re-checked exactly: f=C₁v, g=b²v, v=αf+βg in R~[a^{−1}]).
- **Base change.** Flat base change gives G~=R~[τ,v/τ^n]. Its presentation R~[τ,V]/(τ^nV−v) is exact: reducing τF=(τ^nW−v)B mod τ forces τ|B. The fiber weights are wt(v)=wt(V)=2 and wt(τ)=0.
- **Lift.** Source Prop. linearization is a general theorem for a smooth integral affine base and an arbitrary line bundle. Spec G is smooth and integral for every n (§3.3), and Spec G~ is the complement of the zero section of the pulled-back bundle. No invariance D₀(R)⊂R is assumed anywhere.
- **Homogeneity.** The homogeneity argument of source Prop. homogeneous-lift is n-independent. σ_λ fixes R=G₀, so its lift is σ_λ⊗id with τ↦λ^{−1}τ and V↦λ^nV. This lift is linear on L=Z×_Y L_Y, and uniqueness of the normalized lift gives σ~D~σ~^{−1}=λ^jD~. I re-derived this rather than assuming an n-version (see O1).
- **(4.1) homogeneous pieces.** A degree-e monomial τ^iV^h has nh−i=e. For e≤0 it equals τ^{−e}v^h. For e>0, with q=⌈e/n⌉ we have h≥q, and it equals τ^{nq−e}V^q v^{h−q} with exponent i−n(h−q)=nq−e≥0. The reverse inclusions are clear. Hence every positive piece is divisible by V, and factorial closure gives δV=0.
- **Fixed τ (δτ=0).** Then δr=τ^{−j}E(r). E is an LND with fiber shift 0, E(v)=τ^jδ(τ^nV)=0, and E≠0 because R~, τ and V generate G~.
- **Moving τ (δτ≠0).** δτ∉τG~. Degree j−1<0, or j−1>0 not divisible by n, puts δτ in τG~ by (4.1). So j−1=nq with q≥0, and ⌈j/n⌉=q+1 gives the multiplier τ^{n−1}V^{q+1}. E is a derivation with fiber shift −2(q+1)<0, and E is locally nilpotent because the order drops by 1+(n−1)m≥1 each step.
- **Orders.** δv=nτ^{n−1}Vδτ≠0, so E(v)≠0. Then ν(E v)=nm−1−(n−1)m=m−1, and ν(E²v) would be (2−n)m−2≤−2. So E²v=0 for every n≥2. At n=2 this reproduces the source's −2, and for large n it is more negative. The extraction fails at n=1, which is outside the scope.
- **Rigidity interface.** In both cases E is a nonzero LND of the *unchanged* R~ with a fixed fiber shift ≤0 and E²(v)=0 for the *unchanged* v and weights. That is exactly the hypothesis excluded by source Prop. rigidity, stated as is. Hence ker D⊂S for every nonzero LND D, so DK(A)⊂S.

### 3.5 Lower DK inclusion (§5)

- The derivations p^N∂_x, p^N∂_y and p^N∂_z are LNDs of A[p^{−1}] because p is invariant. They preserve A once they map the five generators into A. On A[p^{−1}]=C[p^{±1},x,y,z], u=(xy−z(z+1))/p^{n+1} is not free, so the partials carry chain-rule u-terms (for example ∂_x u=y/p^{n+1}). Clearing then needs N=2n+1, which suffices and is attained on the generators for each of x, y, z (checked exactly for n=2..7; the general bound follows from the terms u³/p^n in F and xu³ in J). The candidate's "sufficiently large N" is correct. Their kernels contain p, x, y and z.
- For u: δ₁ kills xy−z(z+1)−p^{n+1}u. Its values are δ₁s=2z+1, δ₁F=−2s(2z+1)/p^n and δ₁J=−2xz/p^n (checked exactly). So p^nδ₁ is a nonzero LND of A with u in its kernel.
- Hence S⊂DK(A), and DK(A_n)=S_n. Since F∉S=F₀A, DK(A)≠A, so A≄C^{[4]}.

### 3.6 Canonical morphism (§6)

My derivation is slightly different from the candidate's but equivalent. A/pA=C[s,u,F,J]/(x₀²F−(1+2sx₀)J)≅C[s,u][M]. The map R→A/pA sends x↦x₀, y↦s+x₀s², z↦sx₀, u↦u. Its kernel is exactly I, with R/I≅C[s,u]: the two compositions are identities modulo I (checked exactly). So A/pA≅(R/I)[M] as an R-algebra.

For q∈V(p)⊂Spec S, the fiber is empty if q⊉I and A¹_{κ(q)} if q⊇I. Neither is Spec κ(q). An isomorphism over an open U forces every fiber over U to be Spec κ(q), so no point of V(p), closed or not, lies in the isomorphism locus. Isomorphism is local on the target, so the maximal such open is well defined, and it equals D(p).

An abstract isomorphism φ: A_n→A_m maps DK onto DK, giving ψ: S_n→S_m that intertwines π_n and π_m. So Spec ψ carries V(p_m) onto V(p_n). Since both ideals are prime, ψ(p_nS_n)=p_mS_m, so ψ(p_n)=c·p_m with c∈S_m^*=C^*. Therefore φ(p_n^rA_n)=p_m^rA_m, ψ(J_r^{(n)})=J_r^{(m)}, and the induced isomorphism R→R carries Jbar_r^{(n)} onto Jbar_r^{(m)} for every r.

### 3.7 Staircase (§7)

- **Upper inclusion.** Let b∈J_r with nonzero residue. Then ord_p(b)=0 by (3.1). This uses ord_p on S, not divisibility in A, so the two filtrations are used correctly. Write b=p^ra with a∈A; then deg a=r and in(a)=b̄τ^{−r}∈G_r. Exactness of gr A=G (§3.3) gives G_r=Σ_{nk−i=r, i≥0} I^kτ^{−r}=I^{⌈r/n⌉}τ^{−r}.
- **Lower inclusion.** p^nF=x−s²−u³ and p^nJ=z−sx lie in S with residues f and g. Their k-fold products lie in p^{nk}A∩S⊂J_r for k=⌈r/n⌉.
- **Strictness.** R/I≅C[s,u]≠0 and I≠0. Localizing at a maximal ideal containing I, Nakayama gives I²≠I, so I^k⊊I for k≥2.
- **Recovery of n.** {r: Jbar_r=Jbar_1}={1,…,n}, so n=max{r: Jbar_r=Jbar_1}. This set is invariant under the induced isomorphism of §3.6, so A_n≅A_m implies n=m.

## 4. Objections

Required: **none.**

Optional (presentation or verifier hygiene; none affects correctness):

- O1. **§4 lift homogeneity is stated in one sentence.** Write out the explicit lift σ~_λ=σ_λ⊗id (τ↦λ^{−1}τ, V↦λ^nV). State that it is a linear automorphism of L=Z×_Y L_Y. Then give the conjugation identity, so it is visible that source Prop. homogeneous-lift is *re-proved* for general n rather than cited as an n=2 statement.
- O2. **§4 cites the induced-LND lemma and the order lemma as "the classical filtered-LND operation, implemented in source047 §3".** Add one line noting that the source proofs use only the exact-representative property (proved here for every n) and the domain/characteristic-zero hypotheses.
- O3. **§6 compresses the fiber computation.** Stating A/pA≅(R/I)[M] as an R-algebra would make both the empty-fiber case and the A¹-fiber case immediate, as would writing R/I≅C[s,u] before §6 rather than in §7. Also state explicitly that the isomorphism locus is a well-defined union, because isomorphism is local on the target.
- O4. **§3 proves ker θ=(H_top) by saying H_top "is irreducible".** Spell out the same UFD argument as in §2 (the reduction mod p is nonzero, and the localization is prime).
- O5. **§3's DVR sentence ("finite order follows from the DVR, or…") is terse.** A one-line justification would help: a local noetherian domain with nonzero principal maximal ideal is a DVR.
- O6. **§7 says "the sum of the ideals I^k over such k is the first of them".** Add that this uses I^{k+1}⊂I^k, and that the degree-r component is read off monomials f^αg^βτ^{i−n(α+β)}.
- O7. **Verifier: `--source-tree` does not check the tree file against its external SHA256 anchor** (eeecc1…). Any tree with `truncated: false` whose entries agree with the anchored local bodies is accepted. This is identity-only and does not affect the mathematics. My `blob-check.py` anchors the tree hash and compares it independently.
- O8. **Verifier: `controls.py` never exercises `--source-tree`.** My `author-source-controls.py` covers this layer with 8 copied cases, all correct.
- O9. **§5 leaves N implicit.** A manuscript should state that u is not a free coordinate of A[p^{−1}], include the chain-rule term, and record N=2n+1. A first draft of my own check made exactly this slip (it treated u as free) before I corrected it, so the explicit statement guards against a natural misreading.

## 5. Validation run by this reviewer

- **Exact identity checks.** `algebra-check.py` is pure Python over Q, with no CAS installed. It ran 57 distinct identities (163,694 assertions) for n=2..7, plus combinatorial checks of (4.1), the moving-τ shift, the order bookkeeping and the staircase index for n=2..39. Seven deliberately mutated copies (wrong Δs sign, wrong e₀ power, wrong L_*, missing β term, wrong δ₁y, wrong z, and a partial that treats u as free) were each rejected at the expected identity. These are finite checks, not proofs.
- **Independent Git-blob comparison.** `blob-check.py` checks the anchored complete preprints-tree.json, *without* reading the packet receipts. All 21 non-PDF blobs in the three families match the retained private bodies: 11 for source047, and 8+2 for the family049 companions. There are no extra private bodies.
- **Author verifier on the original packet.**
  - Canonical full invocation with `--source-tree`: PASS (17 public, 30 private, 21 blobs).
  - Wrong manifest anchor: FAIL, as expected.
  - Wrong verifier anchor: FAIL, as expected.
  - `--public-only` on the original: FAIL, as expected.
- **Author controls.** `controls.py`, run from a disposable copy in /var/tmp: all 18 cases PASS.
- **Source-layer controls.** `author-source-controls.py` ran 8 copied cases, all correct: positive; resealed private-source edit; truncated tree; extra family blob; altered tree sha; resealed dropped receipt; `--source-tree` with `--public-only`; and resealed proof edit under the old anchor.
- Outputs: `algebra-check-result.json`, `blob-check-result.json`, `author-verifier-runs.json`, `author-source-controls-result.json`.

Hashes, controls and finite checks are identity or support evidence only. They certify no theorem.

## 6. Reading, search and proof limits

- Read in full: AGENTS.md; sources/upstream.json; NEW-TEN acceptance and allocation sections (lines 1–160 and the heading list); and from the frozen packet, candidate-047.md, scope-047.md, source-and-credit.md, reading-limits.md, verify.py, controls.py, verification.md, formal-interfaces.md and checkpoint.md.
- Read in full from source047: sections 02 (construction), 03 (degeneration), 04 (bundle), 05 (reduction) and 06 (rigidity). From section 01, only the main theorem and the stable-coordinate corollary (lines 50–110).
- Not read: source047 section 07, README, main, preamble and references; both family049 companion bodies (they are not used by the proof); and Blanc–van Santen, which bears only on the abandoned pre-freeze idea.
- Primary antecedents read for operative comparison only: Ghosh–Gupta arXiv:2206.15210v5, extracted text lines 1150–1330 (Theorem 4.1 with full proof, Theorems 4.2–4.3, Corollary 4.4); and Ghosh–Pal arXiv:2404.13803v1, lines 230–309 (Theorem 3.2 with proof). Neither is a dependency of the candidate's proof. Their DK classes are polynomial, and their proof recovers exponents by the same contraction strategy that the author already credits. No contribution judgment is made here.
- Viewed only partially: diagnostic.py (output truncated); its result files were not relied on. The manifest's file and directory lists were consumed through the verifier.
- No literature search was performed. This is a proof gate.
- Stipulated, not re-proved: source Prop. linearization (Picard invariance and the normalized lift), source Prop. rigidity (Mason–Stothers and the nonsquare argument), the source principalization torsor and faithful flatness, and the source induced-LND and order lemmas as general statements. Each was checked to apply as stated, with unchanged hypotheses or hypotheses re-verified for all n.
- Third-party bodies remain only in the author's private directory. None is copied into this directory, and none should be staged.

## 7. Seal

The external anchors for this directory's manifest.json and verify.py are reported to the parent separately; the manifest cannot contain its own hash. `python3 -I verify.py --expected-manifest H_M --expected-verifier H_V` checks the following:

- the exact file and directory inventory;
- SHA256 hashes and sizes;
- root and ancestor symlinks, hardlinks, nonregular nodes, and nested manifests.

`controls.py` runs copied mutation controls against those anchors.
