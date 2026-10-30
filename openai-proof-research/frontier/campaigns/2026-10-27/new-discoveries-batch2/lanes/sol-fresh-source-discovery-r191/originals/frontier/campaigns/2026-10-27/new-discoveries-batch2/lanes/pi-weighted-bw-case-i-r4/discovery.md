# discovery.md — pi-weighted-bw-case-i-r4 (2026-10-28)

New mathematical findings of this session, in dependency order. All are elementary consequences of the
reduction W = ω^(−1/2), X = A√ω, Y = B√ω, but their combination appears to be new.

## D1. The deformed commutator is a weighted chain contraction of the wedge

For W = diag(w₁,…,wₙ) and T(X,Y) = XWY − YWX:

    T(X,Y)_{ij} = Σ_{k=1}^n w_k (X∧Y)_{(ik),(kj)},   (X∧Y)_{(ik),(kj)} := X_{ik}Y_{kj} − X_{kj}Y_{ik}.

Consequently Eq. (14) ⟺

    ‖Λ(X∧Y)‖_F ≤ sqrt(w₁²+w₂²) ‖X∧Y‖_F   for decomposable ξ = X∧Y,

Λ: ∧²(M_n) → M_n, Λ(ξ)_{ij} = Σₖ wₖ ξ_{(ik),(kj)} — Λ touches only "chain" wedge coordinates
(col of first index = row of second). Verified numerically (verify_wedge.py, exact to 0.0).

## D2. Λ is NOT bounded by c on the full exterior square

Λ*Λ on the invariant block V_{ij} = span{ e_{(ik),(kj)} : k } has top eigenvalue (Σₖ wₖ)² > c² in general;
exact rational computation: ‖Λ‖²_{∧²} = 98 > 97 (n=3, w=(9,4,1)); 102 > 97 (n=4,5). So the conjecture is a
statement about the *decomposable cone* only — decomposability (Plücker) is indispensable. This kills the
"bound the operator on all of ∧²" route with a proof, not just a heuristic.

## D3. Shear invariance ⟹ the sharpened deficit form is equivalent, not stronger

T is alternating and T(W⁻¹,·) = 0, so (X,Y) → (X, Y − proj_X Y) preserves T and maps
c²(‖X‖²‖Y‖²−|⟨X,Y⟩|²) → itself. Hence
   ‖T‖² + c²|⟨X,Y⟩|² ≤ c²‖X‖²‖Y‖²  ⟺  ‖T‖² ≤ c²‖X∧Y‖².
The "sharpened conjecture" is exactly Eq. (14) in deficit form (verified numerically anyway:
verify_sharpened.py, min eigenvalue ≥ −2e-12 over 400 structured X, n ≤ 6).

## D4. n = 2 is an identity (no centering needed)

‖XWY − YWX‖²_F = (w₁²+w₂²)(‖X‖²_F‖Y‖²_F − |⟨X,Y⟩|²_F) for ALL X,Y ∈ M₂ (symbolic: symb_n2c.py; numeric ~1e-13).
This strengthens the paper's identity (19), which the authors prove for centered pairs
(a₂₂ = −(λ₁/λ₂)a₁₁). Centering is unnecessary because T is shear-invariant (D3).

## D5. Rank-one X: complete SOS and exact operator norm

For X = E_pq, p ≠ q, the deficit D(X,Y) = c²‖X∧Y‖² − ‖T(X,Y)‖² is the explicit PSD form

    D = |w_p Y_qp + w_q Y_pp|² + (c²−w_p²−w_q²)(|Y_pp|²+|Y_qq|²+|Y_qp|²)
        + (c²−w_p²)Σ_{i∉{p,q}}|Y_ip|² + (c²−w_q²)Σ_{j∉{p,q}}|Y_qj|²,

so ‖T_{E_pq}‖² = w_p²+w_q², attained on the top-2 block. The M-matrix diagonal has the clean per-entry form

    ⟨E_ab, M(X) E_ab⟩ = |w_aX_aa + w_bX_bb|² + (c²−w_a²−w_b²)(|X_aa|²+|X_bb|²+|X_ba|²)
                       + (c²−w_a²)Σ_{i≠a}|X_ia|² + (c²−w_b²)Σ_{j∉{a,b}}|X_bj|²,

each coefficient ≥ 0 for a ≠ b (cross term checked to be +2w_aw_bRe(X̄_aa X_bb), i.e. the PSD 2×2 block
[[c²−w_a², w_aw_b],[w_aw_b, c²−w_b²]], det = c²(c²−w_a²−w_b²) ≥ 0).

## D6. Structured 2-sparse families: explicit SOS with (w_p²−w_q²) factors

symb_n3.py (n = 3, symbolic, factored):
- X = E₁₂+aE₁₃, Y = E₂₁+bE₃₁:  D = |w₂X₁₃ − w₃Ȳ₃₁|² + (w₂²−w₃²)(|Y₃₁|²+|X₁₃Y₃₁|²) + w₁².
- X = E₁₂+aE₂₃, Y = E₂₁+bE₃₂:  D = |w₁X₂₃ + w₃Ȳ₃₂|² + w₂²|X₂₃|² + (w₁²+w₂²−w₃²)|Y₃₂|² + (w₁²−w₃²)|X₂₃Y₃₂|².
- X = E₁₂+aE₁₃, Y = E₂₁+bE₃₂:  D = aāb̄b(w₁²+w₂²−w₃²) + aāw₂² + b̄bw₁² + bb̄w₂² (all coeff ≥ 0).
- X = E₁₂+aE₁₁, Y = E₂₁+bE₂₂:  D = aāb̄b(w₁²+w₂²) + aāw₂² + b̄bw₁² (≥ 0).
The recurring shape: Lagrange pieces per T-entry plus (w_p²−w_q²)·(bilinear)² terms. Note the conjugates:
bilinear forms of type w_pX_{pq} − w_qȲ_{rs} occur (mixed linear/anti-linear), which is consistent since the
deficit is a real quartic in the 4n² realified variables.

## D7. Adversarial numerics (this session)

final_sweep.py, seeds fixed: max ratio ‖T‖²/(c²‖X∧Y‖²) = 0.849 (n=6), 0.824 (n=8), 0.760 (n=12); worst family
= top-2 block plus small leaks, ratio → 1 as leak → 0. No violation anywhere; equality approached only on the
top-2 coordinate block (D5).

## The open crux

Prove for decomposable ξ:
   Σ_{ij}|Σₖ wₖ ξ_{(ik),(kj)}|² ≤ c² Σ_{α<β}|ξ_{αβ}|².
Exact identity available: Σ_{ij}[c²Σₖ|ξ_{(ik),(kj)}|² − |Σₖwₖξ_{(ik),(kj)}|²]
   = Σ_{ij,k<l}|w_lξ_{(ik),(kj)} − wₖξ_{(il),(lj)}|² − (Σ_{k≥3}wₖ²)Σ_{chains}|ξ|²,
and Plücker gives ξ_{(ik),(kj)}ξ_{(il),(lj)} = ξ_{(ik),(il)}ξ_{(kj),(lj)} − ξ_{(ik),(lj)}ξ_{(kj),(il)}.
Naive coefficient bookkeeping loses a factor n (each non-chain coordinate meets n values of the free index).
Next tool: numerical SDP for a rational Gram decomposition at n = 3, then pattern extraction.
