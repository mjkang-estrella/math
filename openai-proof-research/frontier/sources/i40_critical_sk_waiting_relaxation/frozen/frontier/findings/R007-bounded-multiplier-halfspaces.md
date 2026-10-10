# R007 — Invariant half-spaces for all bounded multiplier variants

Date: 2026-10-08. **Validated construction obstruction under the accepted pinned corpus.** Independent round-6 audit passes without substantive correction. This closes the specified bounded-multiplier family as a route to an ordinary invariant-subspace counterexample. It is not counted as a demonstrated substantial new-to-literature advance.

The [full proof](../iterations/i04-operator-asymmetric.md), [independent audit](../reviews/i04-operator-asymmetric-r6.md), and [parent verification](../sources/i04_operator_asymmetric_r6/parent-verification.json) are part of this finding. Pin: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## 1. Exact operator family and theorem

Let `X=Z₂` with Haar probability, `E=L²(X;C)`, and `H=ℓ²(Z;E)`. Use exactly the weights, translation, and infinite normalizer in the pinned manuscript *Backward intertwiners and a transitive commutant*. Their formulas are repeated here to fix the family.

For `m≥1`, put `N_m=2^m`, `I_m=[8^(m−1),8^m)∩Z`, `T_m(x)=x mod N_m`, and `J_m=100(N_m−2)`. Set `a₀⁺=a₀⁻=10`; for `k∈I_m`, set

\[
 a_k^+(x)=10(k+1)+J_m+100T_m(x),\qquad
 a_k^-(x)=10(k+1)+J_m+100(N_m-1-T_m(x)).
\]

Let `a_j=a_j⁺` for `j≥0`, `a_j=a_(−j−1)⁻` for `j<0`, and `β_j=e^(−a_j)`. Define `w₀=1`, `w_(j+1)=β_j w_j` for every integer `j`. Define `b̃₀=1` and

\[
 \widetilde b_{j+1}(x)=\widetilde b_j(x)
 \frac{\beta_{j-1}(x+1)}{\beta_j(x)},\qquad
 L(x)=\sup_{j\in\mathbb Z}\widetilde b_j(x).
\]

The source supplies a translation-invariant conull set `X_*` on which `1≤L<∞`. Put `b_j=b̃_j/L` there and zero off it. The bounded operators are

\[
 (Sf)_j(x)=\beta_{j-1}(x)f_{j-1}(x),\qquad
 (Vf)_j(x)=b_{j+1}(x-1)f_{j+1}(x-1).
\]

**Theorem.** For every measurable `r:X×Z→C` with finite essential bound, let `M_r` multiply by `r` at the output coordinate and base, and put `Q_r=S+M_r V`. Then

\[
 \mathcal M_r=\overline{\operatorname{span}}^{\,H}
 \{Q_r^n(u\otimes e_0):u\in E,\ n\ge0\}
\]

is closed, invariant, infinite-dimensional, and of infinite codimension. Thus every member of this family has an ordinary invariant half-space, including arbitrary complex phases, zero coefficients, and base-dependent coefficients. No positivity or lower bound on `r` is required.

The forward shift, backward intertwiner, normalizer, and coefficient placement are fixed exactly as above. The theorem makes no assertion for unbounded coefficients, changed transports or weights, another normalization, or arbitrary nonlocal perturbations.

## 2. Source contracts

The primary directory is `preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/build/sections/` at the pin:

- [`weights.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/build/sections/weights.tex): `eq:a-plus`, `eq:a-minus`, `eq:bilateral-a`, the all-index definition of `w_j` in `prop:fibers`, `eq:a-error`, and `prop:normquasi`.
- [`intertwiner.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/build/sections/intertwiner.tex): `eq:b-recursion`, `eq:b-positive`, `eq:b-negative`, `lem:normalization`, `eq:commuting-coefficients`, `eq:V-definition`, and `prop:V`.
- `introduction.tex`, `thm:direct-model`, and `conclusion.tex` distinguish the transitive larger algebra from an individual operator's ordinary invariant subspaces. The companion *Invariant projection counterexamples for every irrational rotation*, `build/00-introduction.tex`, `thm:main`, and `build/product-structure.tex`, `p:prop:joint-structure`, concern factor-affiliated projections and do not exclude the spaces constructed here.

The [six-file source manifest](../sources/i04_operator_asymmetric/upstream_manifest.json) records all immutable URLs and hashes. No external invariant-subspace theorem is a logical input to this construction. The source theorems are accepted as stipulated, not audited for upstream truth.

## 3. Proof

**Coordinate identity and decay.** Define `Cg(x)=e^(−10)L(x−1)⁻¹g(x−1)`. The two recurrences imply

\[
 \frac{b_j(x)w_j(x)}{w_{j-1}(x+1)}=\frac{e^{-10}}{L(x)}.
\]

Thus for `h_j=w_j⁻¹ f_j`,

`w_j⁻¹(Q_r f)_j=h_(j−1)+M_(r_j) C h_(j+1)`.

Every fixed-coordinate multiplier is boundedly invertible; their direct sum is not asserted to be bounded. This is a coordinate identity, not a global similarity. For each fixed `r`, intersect the source conull set with all integer translates of the countably many coordinate sets where its bound holds.

For `N=2^m`, on the cylinder `T_m=N−1` the actual source formula for `b̃_(8^m)` gives

\[
 \log L\ge K_m=700(2^m-1)8^{m-1}
 =\frac{175}{2}(N-1)N^3.
\]

This lower bound uses one coefficient of the true infinite supremum. If `N≤n<2N`, a segment of `n` consecutive base translates contains this residue. Since every other `L` factor is at least one,

\[
 \|C^n\|\le e^{-10n-K_m}\le e^{-n^4}\quad(n\ge2).
\]

The bound also holds for `n=0,1`. The fixed-coordinate cost, from `eq:a-error`, is

`||M_(1/w_j)||≤exp(5j(j+1)+400j^(4/3))≤exp(410j²)` for `j≥1`.

**Finite path operators.** Put `B=||r||∞`, `K=2max(1,B)` and

\[
 B_{0,j}=1_{j=0}I,\qquad
 B_{n+1,j}=B_{n,j-1}+M_{r_j}CB_{n,j+1}.
\]

The normalized central orbit has coordinate `B_(n,j)u`, vanishes unless `|j|≤n` and `n−j` is even, and has leading block `B_(n,n)=I`. Each path to `j` has `(n−j)/2` backward steps. Positivity of `C` and `C*` gives separately

\[
 |B_{n,j}u|\le K^n C^{(n-j)/2}|u|,\qquad
 |B_{n,j}^*u|\le K^n(C^*)^{(n-j)/2}|u|.
\]

For the adjoint bound, reverse each elementary product and use `|(M_(r_j)C)*u|=|C*M_(conj r_j)u|≤B C*|u|`. Taking the adjoint of a modulus inequality would not justify this step. No multiplier is commuted through `C`.

**Construct a convergent annihilator.** Given `g∈E`, start with `z_(−1)=g`, and set all other nonpositive and all positive even coordinates to zero. Recursively define

\[
 z_{2m+1}=-B_{2m+1,-1}^*g
 -\sum_{s<m}B_{2m+1,2s+1}^*z_{2s+1}.
\]

The leading identity block solves each new odd moment. Let `A_(−1)=1`, `A_m=∏_(s=0)^m(1+K^(2s+1))`, and `c_m=K^(2m+1)A_(m−1)=A_m−A_(m−1)`. Induction yields

\[
 |z_{2m+1}|\le c_m(C^*)^{m+1}|g|,
 \qquad A_m\le2^{m+1}K^{(m+1)^2}.
\]

Indeed the previous terms' powers add to `m+1`, and their scalar constants sum to `K^(2m+1)(1+Σ_(s<m)c_s)=c_m`.

Define `(J_r g)_j=M_(1/w_j)z_j`, with this operator order. Its negative coordinate is `e^(−10)g`. For `k=m+1`, the positive coordinate map has norm at most

\[
 t_m(K)=2^kK^{k^2}\exp\{410(2k-1)^2-k^4\}.
\]

Put `D_K=1640+log K+log 2`. Then `log t_m≤−k⁴+D_K k²≤−k⁴/2` whenever `k²≥2D_K`. Both `Σt_m` and `Σt_m²` converge. Consequently `J_r:E→H` is bounded in the original norm, and `||J_r g||≥e^(−10)||g||`. Its range is closed and infinite-dimensional.

Every pairing with a central orbit is finite. Even moments vanish by parity; for `n=2m+1`, positivity of the real weights cancels the coordinate multipliers, and the pairing vanishes by the defining recursion and `B_(n,n)=I`. Hence `ran J_r⊆M_r⊥`. The orbit closure is invariant by boundedness of `Q_r`, contains `E⊗e₀`, and its orthogonal complement contains the infinite-dimensional range of `J_r`. This proves the theorem.

## 4. Additional conclusions only for the exact asymmetric operator

For `r_j=d_j`, with `d_j=1` for `j≤0` and `d_j=2` for `j≥1`, write `Q=S+RV`. The [full proof §6](../iterations/i04-operator-asymmetric.md#6-eigenvectors-and-adjoint-kernels-checked-directly-for-q) and [audit §6](../reviews/i04-operator-asymmetric-r6.md#6-spectral-and-ideal-claims-for-the-exact-asymmetric-q-pass) also establish `σ_p(Q)=σ_p(Q*)=∅`. The Gaussian power bound excludes nonzero eigenvalues; direct two-step kernel recurrences force nonsummable growth toward the positive end for `Q` and negative end for `Q*`. Haar translation and Tonelli justify the pointwise-to-Hilbert-space step.

Thus this exact `Q` has dense range, no nonzero finite-dimensional invariant subspace, and no proper closed invariant subspace of finite codimension. Positivity, solidity and source transitivity exclude nontrivial invariant lattice ideals. All these statements coexist with its ordinary invariant half-space. They are not appended to arbitrary complex or vanishing `r`.

The exact asymmetric case also has the explicit bounded row `F=J*` in the full proof, yielding another half-space `∩_(n≥0)ker(FQ^n)`. No equality with the central orbit closure, classification of all invariant subspaces, projection formula, or bounded global normalization is asserted.

## 5. Validation, prior art and disposition

The independent audit passes the convergence, adjoint order, arbitrary bounded complex extension, and exact asymmetric spectral claims. Parent review read the source weights and intertwiner, checked the quartic-versus-quadratic bound and telescoping recursion, and reproduced both scripts. Original output was byte-identical. Independent Gaussian-rational tests covered seven models, including zero coefficients and noncommuting complex coefficients: 1,932 forward and 1,932 adjoint path bounds, 77 triangular bounds, 161 annihilator identities, 161 original-coordinate pairings, and 1,932 orbit comparisons. Deliberately reversing the adjoint order failed in three models; dropping conjugation failed in four. Another 142,817 logarithmic identities, 71,400 inverse-weight bounds and 32,764 dyadic-cover checks passed.

The parent verified six pinned files against the complete source tree, three cached literature files, 29 author artifacts and 16 reviewer artifacts. Only the shared iteration index changed from the reviewer's input snapshot before integration. Finite models do not prove infinite-dimensional convergence and do not replace `L` with a finite normalizer. The proof above and independent AI audit supply the mathematical validation, not a proof-assistant certificate or external peer review.

From `openai-proof-research/`, reproduce with:

```bash
python3 frontier/experiments/i04_operator_asymmetric_r6/reproduce_original.py
python3 frontier/experiments/i04_operator_asymmetric_r6/independent_checks.py
```

Moment and tridiagonal methods are established techniques. The bounded primary-source screen found no exact duplicate of this normalizer-driven construction, but did not establish priority; its access limits are preserved in the audit. The new-to-project contribution is the uniform use of this exact infinite normalizer to make a triangular annihilator converge in the original norm.

**Decision:** close the entire fixed `S+M_rV` bounded-multiplier family as an ordinary-ISP counterexample route. Do not launch another coefficient variant. This is one validated obstruction, strengthening R005's commuting-family obstruction, and does not satisfy the substantial-new-progress objective by itself.
