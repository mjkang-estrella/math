# progress.md — pi-cauchy-strict-discovery-r1

Solo lane. Pi GLM-5.3-Flash (thinking=high), standard speed. No children, no writes
outside this lane, no git operations, no external messages.

## Timeline (2026-10-28)

1. **Read standing context.** Ancestor `openai-proof-research/AGENTS.md`, batch
   `AGENTS.md`, `ledger.json` (accepted = 0 additional; 30 prior intact),
   `prior-campaign-context.json` (30 accepted; none on Cauchy/stable kernels or strict TP
   of Gram-type kernels). Confirmed the two live sibling jobs (gamma series-level formal,
   arcsinh review) were left untouched.
2. **Read root-special-screen-r6 artifacts** (`FINDINGS.md`, `post-325521.json`,
   `simon-cauchy.html`, `simon-stable.html`, `provenance.json`): actual MathDB snapshot
   (open, empty solutions) and both Simon preprints.
3. **Read both source bodies in full** (HTML→text extraction): 1305.1173 Theorem
   (a)/(b)/(c), Conjecture (2), Prop 1, Section 5 (n=4,5 partials, Conjectures 1–4,
   ASM generating function), Section 6 Corollary; 1412.0132 Theorem 1, Corollary 1,
   §2.1 (Lemma 1 local limit theorem, beta-kernel reduction to `(y-x)_+^{1/α−2}`, Karlin
   Thm 3.2.1), §2.2 (the displayed Gram convolution formula), Remark 1 (I_β never STP_n),
   Remark 2(a),(b) (STP_n for α<1/n explicitly left open).
4. **Derived the route and stress-tested it.** Key steps: the J_α convolution identity,
   Andreief, analyticity via the Zolotarev series, nonvanishing asymptotics of `D_x`.
   Found and **discarded** one derivation (termwise series integration of `J_α`):
   `Σ_k |c_k| ∫_0^1 v^{-αk} dv` diverges for `k ≥ 1/α` — invalid Fubini; its numerical
   prediction (double sum vs closed form, relerr ≈ 0.5) exposed the error. Replaced by
   the Mellin/Fourier derivation (autocorrelation of the log-density; FT =
   `sinh(πξ)/(α sinh(πξ/α))`), verified analytically and numerically to 1e-18.
   This was the "wrong transform" trap anticipated in the brief.
5. **Verified the error analysis of the asymptotics**: leading layer `{1..m}` isolated by
   exponent gap `αU`; all other injective tuples suppressed; non-injective tuples give
   zero determinants; leading coefficient `∏_{k≤m} c_k · det R · det C ≠ 0` via the
   ordinary-Vandermonde reduction `det[z_i^{αk+1}] = (∏ z_i)·Vandermonde(z_i^α)`.
   No extra α-restriction beyond `αm < 1` (the cruder truncation bound `α(m²−m+2)/2 < 1`
   first derived is dominated by the exact-series argument; for m ≥ 3 it is implied by
   `α < 1/m` anyway).
6. **Numerical diagnostics** (scripts/check_fast.py, check_final.py; logs in scripts/):
   all pass as described in SUMMARY.md. Two script bugs were found and fixed along the
   way (exact-zero series terms triggering premature convergence stops — `sin(παk) = 0`
   at even k for α=1/2; an `(n,n)`-shaped accumulator vs scalar in the discrete
   Cauchy–Binet check — the identity itself held to 1e-12).
7. **Prior-art screen** (bounded; all 2026-10-28):
   - Semantic Scholar citations of JAT DOI 10.1016/j.jat.2014.05.014 (7) and of
     1412.0132 (1): none resolves the strict conjecture; 2026 citers (2608.28376,
     2607.02828) read at abstract level — unrelated.
   - Simon's complete publication list (univ-lille): no TP work after Constr. Approx.
     2016; no resolution.
   - 2006.16213 (preservers), 2607.02778 (spectral Darboux / Toeplitz smoothing
     strictification — Bessel kernel + PF sequences only), 2606.31647 (Hankel) — none
     covers the Cauchy kernel or supplies a black-box strictification for TP-only factors.
   - Publisher page (ScienceDirect via doi.org) still displays the Conjecture.
   - MathDB 325521 open/empty (snapshot reused; not novelty evidence on its own).
8. **Wrote deliverables**: discovery.md, PROOF.md, SUMMARY.md, provenance.json.
9. **Lean**: no lean/elan/lake toolchain present in the lane environment; no compilable
   artifact attempted (also per the brief: no heavy formalization before gates). Honest
   module plan + dependency inventory in SUMMARY.md/PROOF.md; **no formal PASS claimed**.

## Open items for root

- Independent adversarial review of PROOF.md (esp. Lemma 3.1 FT argument, Lemma 5.1 error
  layering, and the use of Theorem A via the `(0,∞)` reparametrization).
- The Karp 1509.05120 / MathDB 331384 second lead was NOT investigated (main task
  survived the screens; per brief, secondary lead only if main excluded).
- If accepted: paper + extracted replay + formal endpoint are root-level follow-ups.
