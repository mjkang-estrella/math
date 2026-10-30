# T117Q independent proof review, round 1

Role: independent full-scope proof reviewer. Verdict concerns the proof only. No contribution, novelty, acceptance or count verdict is given here.

**Verdict: PASS_FULL_T117Q.** Every quantifier of the frozen scope has a complete proof in the sealed candidate. I found no required gap. Optional editorial improvements are listed separately in §4; none is a precondition of this verdict.

## 1. Inputs and authentication

| Item | Value |
|---|---|
| Author packet | `frontier/campaigns/2026-10-14/fresh-structural-discovery-r59/` |
| `MANIFEST.json` SHA256 (external anchor) | `053986e5a446cd18251b3e3e8b917bc58cafb0f68d6de87562fe190766e28ae2` (matches) |
| `candidate.md` | `e32f7a12592e237b5bb428aa7cb0f9f29d01739b6c3230ceb2fcca15129aeea4` (matches) |
| `original-scope.txt` | `fc5a8f872843cd4c0448c6fb6ba4864cf17044f6ab7366d3010ca551ebdbfe36` (matches) |
| `checkpoint.md` | `0a9a452638864f288e9185c29f9aa73ceb77858d683c1329211750916679fab2` (matches) |
| Upstream pin | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (`sources/upstream.json`) |
| Canonical tree | `sources/preprints-tree.json`, SHA256 `eeecc1da…dc5e09b`, 13223 entries, `truncated: false` |

Order of operations. The manifest digest was checked against the externally supplied anchor before its inventory was trusted. An independent stdlib walk (not the author verifier) then confirmed 52 payload files plus `MANIFEST.json`, 12 directories, no extra or missing paths, and every byte count and SHA256. The author verifier was read in full and then run read-only (`python -B`): positive anchor PASS, all-zero wrong anchor FAIL with `external manifest anchor mismatch`.

Source identity. `checks/source_blob_check.py` (reviewer code) recomputes Git blob SHA-1 of every actual local body under `private/source117-1` and `private/source117-2` and compares with the complete canonical tree, not with the author's receipts. Result: 20/20 match in blob SHA and size. In each companion the canonical tree also has a PDF and `README.md` that were not retrieved; neither is needed. Output: `checks/source-blob-check.json`.

Source truth at the pin is stipulated. Only new deductions and exact interfaces were validated.

## 2. Frozen scope checked

`original-scope.txt`: absolute c>0; genuine finite negative-type metrics (V_j,d_j), n_j=|V_j|→∞; for every complex Hilbert space H (any dimension, nonseparable allowed, no rank relation to n_j) and every F:V_j→S_1(H) with ‖F(x)−F(y)‖_1≤d_j(x,y), the ordered uniform-pair average of ‖F(x)−F(y)‖_1 is at most c^{-1}(log log n_j)^{9/2}/√(log n_j) times the ordered uniform-pair average of d_j. The metric is positive on distinct points, satisfies all triangles and is a squared Hilbert distance. No efficient/rational claim. No bounded-dimension, commutative, weighted-only or weaker-exponent rescue.

`candidate.md` §Statement states exactly this, writing C for c^{-1}. The candidate makes no weaker substitution anywhere: the final metric is uniform on copies, genuine, negative type, and the exponent is 9/2.

## 3. Audit of the seven required points

### 3.1 Wick pairing register contraction (Lemma 1)

Isserlis' formula holds with repeated indices, so E(Σg_jX_j)^{2q}=Σ_π W_π, where W_π sums the words over free labels of the q blocks of the pairing π. With Vh=Σ_i e_i⊗X_i h, V*V=ΣX_i^2≤I, so ‖V‖≤1, and V*(e_i⊗h)=X_i h uses selfadjointness. Scanning right to left, a first-seen position applies I⊗V (opening a register); the partner position permutes that register next to H (a unitary) and applies I⊗V* (closing it). Untouched registers are tensored with the identity, so the order in which pairs open and close is irrelevant. **Crossing pairings are handled exactly like nested ones.** Expanding the composition gives exactly W_π. Hence ‖W_π‖≤1 with no positivity assumed for W_π. E(ΣgX)^{2q} is an expectation of positive operators, so 0≤E≤‖E‖I≤(2q−1)!!I. This is a genuine Loewner bound, not a normalized-trace bound. Complex Hermitian entries are fine. **No gap.**

Diagnostic support only: 33 crossing pairing sums were evaluated, 20 of them not PSD, every one of norm ≤1. A control shows that a trace-normalized variance hypothesis does not give the Loewner bound (`checks/review-diagnostics.json`).

### 3.2 Universal degree-2q monomial matching (§2)

- Expansion: with u=G/√m, m^{-q}Σ_{α∈[m]^{2q}}(M̂_α−M_α)X_α, where ‖X_α‖≤1 because X_j^2≤ΣX_i^2≤I. The bound m^{-q}·m^{2q}·2m^{-3q}=2m^{-2q} is correct, and the operator is selfadjoint, so it is ≤2m^{-2q}I.
- Truncation bias: |G^α|≤|G|^{2q}, so (E|G|^{4q})^{1/2}P^{1/2}≤(m+4q)^q e^{-cm/2}≤m^{-3q} for large m, because q=O(log m).
- Hoeffding (source form, requires u≤B, which holds): R=SN=m^{10q+6}, u=m^{-3q}, B=(2√m)^{2q}, giving exponent c·m^{2q+6}/16^q. The union over m^{2q}=e^{O((log m)^2)} words still goes to 0.
- Norm event: SN·2e^{-cm}→0, since log(SN)=O((log m)^2). On it, truncated and untruncated empirical moments coincide, so |M̂_α−M_α|≤2m^{-3q} for all α.
- Final constant: (2q−1)!!/m^q+2m^{-2q}≤(4q/m)^q. I checked this exactly in log form (D in diagnostics).
- Uniformity: the event is a statement about finitely many real scalars, fixed before any matrix exists. The operator bound is then deterministic for every tuple in every dimension. There is no net over matrices and no dependence on the target dimension.
- Source per-chart events (`directions-proof.tex`): Fourier and covariance failures are S·|net|·e^{−cm^4} with log|net|=O(m log m), and the norm failure is SN·e^{−cm}. All go to 0 with log S=60(log m)^2(1+o(1)). Nonparallelism holds almost surely. The majority-chart property is not used, so the S/2 averaging in `contraction.tex` is entirely replaced by Lemma 2.
- Parameters: N=m^6, q=⌈log N⌉, S=m^{10q}, and N^{1/q}≤e. **No gap.**

### 3.3 Selector, Lemma 2 (§3, §8)

- Bessel: L^2(γ;C^D)=L^2(γ)⊗C^D, and the g_j⊗e_k are orthonormal. Hence Σ_j‖X_jv‖^2≤E‖U(g)v‖^2≤‖v‖^2 and ΣX_j^2≤I. The X_j are selfadjoint.
- Positivity: Y=ΣA_jX_j=E[A sign A]=E|A|≥0 and TrY=E‖A(g)‖_1. Positivity is asserted only for Y, never for individual summands.
- Operator concavity of x^{1/q} for convex combinations gives S^{-1}ΣQ_s≤N^{1/q}(4q/m)I≤4eq/m·I. Also I−P_s=1_{(h,∞)}(Q_s)≤Q_s/h, so ΣP_s≥(S/2)I.
- Monotonicity: Z_si^{2q}≤Q_s^q, and (Z_si^{2q})^{1/q}=Z_si^2, so Z_si^2≤Q_s and ‖Z_siP_s‖^2≤h. §8's integral representation correctly yields both monotonicity and concavity.
- Trace step: (S/2)TrY≤Tr(YΣP_s), because Y≥0 lets us write Tr(Y^{1/2}(ΣP_s)Y^{1/2}). Each Tr(YP_s) is real and nonnegative. Its expansion Σ_iTr(b_siZ_siP_s)+Σ_jTr((A_j−A_sj)X_jP_s) is bounded termwise in absolute value using ‖X_jP_s‖≤1. The noncommuting P_s are never diagonalized together.
- Result: TrY≤2Nt√h+2e, with √h=√(8eq/m). The constant is absolute. **No gap.**

Diagnostic support only: under a finite law with exact Gaussian moments, the full chain holds. A badly scaled chart receives a rank-0 selector, and null-space coefficient perturbations make some individual summands negative or nonreal while the summed inequality holds.

### 3.4 Changed-parameter source audit (§4)

I enumerated every occurrence of S, ε and τ in source117-1 by search and re-derived each one at the new values ε=m^{-200}/S and τ=m^{-2000}/S^2:

- Auxiliary Fourier mass: εSN=m^{-194}. The distance error 4εSN log(b/a) and the gradient mass 2εSN√m/a≤1 still hold.
- D^j p bounds (j≤2) remain ≤m^{110}: the first component is unchanged, and the auxiliary term is m^{-194}·O(log m)·(2√m/a)^{2j}.
- A_s^0 columns are orthogonal (disjoint summands), with norm (m/N)ε^{-1/2}√log(b/a)=√S·m^{95+o(1)}. DA_s^0 gains the same √S factor. A_s=A_s^0(I−JJ^+)+DpJ^+ and DA_s=DA_s^0(I−JJ^+)+D^2pJ^+, so all five strong bounds are ≤√S m^{300}.
- Profile (ker:profile) is unchanged. √ε·ε^{-1/2} cancels in ⟨A_s^0e_i,p(η)⟩=(m/N)∫sin⟨g,w⟩dσ/σ. The residual uses the per-chart Fourier lemma with |w|≤6m^{40.5}<m^{42}, plus the gradient mass ≤1, and |J^+e_i|≤4m/N.
- Rounding: |J^+x−θ|≤2√mτ and |Q x|≤√Nτ give a feature error ≤√S m^{305}τ. The squared-distance error is ≤C√S m^{415}τ≤S m^{610}τ=m^{−1390}/S≪r.
- Local angle: the DA_s operator term is ≤2√S m^{300.5}τ‖h‖ (≲√S m^{411}τ after pairing with |P_y|≤2m^{110}), and replacing P_y by p(η) costs ≤S m^{605}τ. Both are ≪(m/N)log m, so L=C_0 log m is unchanged. The global angle ≥−r is unchanged.
- Repair (`repair.tex`) is stated for an arbitrary finite chart partition and needs no change. Positivity holds: within a chart δ>0 gives |q_v−q_w|^2>0, and across charts the distance is 8r.
- Adjacency: δ=L(m/N)τ, log(r/δ)=1997 log m+2 log S−log(C_0 log m)=O((log m)^2). Hence d≤δ+8δ(1+log(r/δ))≤Cτ(m/N)(log m)^3.
- Count: H_0=N(1+8√m/τ) with log H_0=O((log m)^2), so |V|≤S(H_0+1)^m=exp(Cm(log m)^2).
- (4.2), the diameter ≤Cm, and the first-chart average ≥cm follow as in `metric.tex`.

No S=m^3 proposition is invoked unchanged. **No gap.**

### 3.5 Matrix interface coarea, cube inequality (§5)

- For θ∈T, the kernel support θ+[−λ,λ]^m lies inside U, so the distributional-gradient identity on U applies. The matrix case is entrywise linear.
- The jump across Q_{i,k} is F of two labels differing by τe_i, so ‖Δ‖_1≤Cτ(m/N)(log m)^3. Intersections of nonparallel hyperplanes are H^{m−1}-null.
- With the nonnegative kernel, ‖b_si(θ)‖_1≤Cτ(m/N)(log m)^3·Σ_kh(kτ). The source lattice bound gives τΣh(kτ)≤2. This yields the **pointwise** coefficient budget (5.2) without any scalar decomposition of the target.
- Mismatch: ‖∂_jH_s−∂_jH_1‖_1≤Cr/λ by the pointwise ‖f_s−f_1‖_1≤Cr inside U and ∫|∂_jκ_λ|=‖ρ'‖_1/λ. Hence e≤Cmr/λ=Cm^{−5}.
- Lemma 2 with t=C(m/N)(log m)^3 and q≈6 log m gives C√m(log m)^{7/2} at every θ∈T.
- Cube inequality (5.4): (G(t),W(t)) is a rotation of (G,G′), so W(t) is independent of G(t). The coefficients 2φ(G_j(t))/√(2/π) lie in [0,1]. The Gaussian contraction principle (adding independent noise √(1−a_j^2)g′_j, then Jensen) holds in any norm. Integrating over t gives the constant √(π/2), independent of m, D and the norm. H_1 is smooth on R^m.
- The smoothing error ‖H_1−f_1‖_1≤C(mλ+r) is a Bochner triangle inequality, so it is valid in trace norm.
- Hermitian dilation: ‖D(B)‖_1=2‖B‖_1 and D is real-linear, so D(F)/2 is nonexpanding and has identical pair distances. **No gap.**

### 3.6 Uniform copies, genuine metric, exponent (§6)

- k_v≥1 retains every vertex, including zero-weight and other-chart vertices. TV(μ,w)≤|V|/M≤m^{−2}, the product TV is ≤2m^{−2}, and with ‖F(v)−F(w)‖_1≤d≤Cm the change in the average is ≤2C/m.
- d′=d_0+ζ(1−δ_{xy}) is the direct sum of two squared Hilbert distances, a sum of two semimetrics, and strictly positive off the diagonal. It is therefore a genuine negative-type metric.
- ζ≤min(1,d_min)/m^2 with d_min>0, since d is a genuine metric on V. Hence d′(x_v,x_w)≤(1+m^{−2})d(v,w), so G/(1+m^{−2}) is nonexpanding on all of (V,d). Copies are within ζ of their representative, giving the additive 2ζ term.
- Sizes: m^m≤n≤M+|V|≤exp(Cm(log m)^2). Then log log n≥log m and √log n≤C√m log m.
- Exponent: cm/(C√m(log m)^{7/2}) ≥ c′√(log n)/(log m)^{9/2} ≥ c′√(log n)/(log log n)^{9/2}. This is exactly the 9/2 exponent, and n→∞.
- The construction is independent of F. **No gap.**

### 3.7 Arbitrary H (§7)

- The ranges of the finitely many F(x) and F(x)* are separable (trace-class operators are compact), so they span a separable closed K. Each F(x)=P_KF(x)P_K, because K^⊥⊂ker F(x).
- For finite-rank P_k↑P_K strongly, P_kF(x)P_k→F(x) in S_1. This is the standard fact for trace-class T under strongly convergent contractions, via finite-rank S_1-approximation.
- Compression is S_1-contractive, so each compressed map is nonexpanding into M_{r_k}(C) with the same trace norm. Apply the finite bound and pass to the limit in the finite sum.
- No selfadjointness (handled by dilation), finite rank, dimension or separability restriction remains, and nonseparable H is covered. **No gap.**

## 4. Objections

**Required objections: none.**

Optional editorial improvements (not required for PASS):

- E1. Make the reduction order explicit. (6.1) is applied in §6 to an S_1(H)-valued map, which is justified by §7 compression and then the §5 dilation. Either move §7 before §6 or add one sentence stating the chain: compress, choose a representative, dilate, apply the selfadjoint bound.
- E2. §2: replace "after dividing by m^q" with "after the factor m^{−q} from u=g/√m". Also state ‖X_α‖≤1 from X_j^2≤ΣX_i^2≤I, and note that Hoeffding needs u≤B, which holds.
- E3. Lemma 1: state that Isserlis' formula is used with repeated indices, so the expectation is exactly the sum of the pairing word sums.
- E4. §4: say that p, Dp and D^2p need no √S factor. Display DA_s=DA_s^0(I−JJ^+)+D^2pJ^+, and separate the two local-profile error sources (≲√S m^{411}τ and ≲S m^{605}τ). The current single bound C S m^{610}τ covers both.
- E5. §5: state the normalized contraction coefficients 2φ(G_j)/√(2/π)∈[0,1] and the resulting constant √(π/2).
- E6. §7: cite or sketch the strong-convergence S_1 fact, P_kTP_k→T.
- E7. Statement: write c^{-1} as in original-scope.txt, or say C=c^{-1}.
- E8. Lemma 2: the explicit constant 2√(8e) may be recorded.

## 5. Validation run by this reviewer

- Independent manifest inventory and hashes (stdlib): PASS. Author verifier read in full, then run read-only: positive anchor PASS, wrong anchor FAIL.
- Independent canonical-tree blob comparison: 20/20 (`checks/source-blob-check.json`).
- Author `checks/integrity_controls.py` was read in full. It ran **only** on a disposable copy at `/var/tmp/t117q-proof-r1-lgJwz2/packet` after the copy's manifest was authenticated against the external anchor. Scratch was `<copy>/checks/scratch-proof-r1`. All 13 controls behaved as expected with matching reasons (`checks/author-integrity-controls-replay.json`). The copy re-verified PASS afterwards. Canonical author bytes were never mutated, and `diff -r` confirmed the copy was identical before the controls.
- Author `checks/matrix_diagnostics.py` was read and replayed with `/tmp/agvenv/bin/python` (Python 3.14.7, NumPy 2.5.3). Status PASS, and its JSON content equals the recorded `matrix-diagnostics.json` (`checks/author-matrix-diagnostics-replay.json`). System `python3` lacks NumPy. This is an environment limitation only.
- Reviewer diagnostics `checks/review_diagnostics.py` (independent code, seed 20261018, same interpreter): PASS. It covers crossing and nested pairings, the Lemma 2 chain with non-minimal coefficients, the trace-norm cube inequality by Monte Carlo, and exact exponent bookkeeping.
- Scope of the diagnostics: finite floating-point checks only. They do not establish the arbitrary-dimension, all-size theorem and are not proof dependencies.
- Copied mutation controls for this review packet: see `checks/review-controls.json`.

No checksum is mathematical or novelty evidence.

## 6. Reading and search limits

See `reading-record.json`. In summary:

- `candidate.md` and `original-scope.txt` were read in full.
- All eight operative TeX files of source117-1 were read in full.
- source117-2 bodies and `figures/construction.tex` were not read beyond identity and a term search. They are not dependencies.
- No primary-literature PDF or text, no campaign-history search, and no web search was performed. These matter only for contribution, which is outside this role.
- The parallel reviewer draft was not read.
