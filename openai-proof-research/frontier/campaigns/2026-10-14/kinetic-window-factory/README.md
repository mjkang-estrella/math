# I340 kinetic window: Factory/Opus fallback

Date: 2026-10-14. Pin: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Role: research sub-agent run through the Factory/Opus 5.5 fallback after a
direct Claude rate-limit failure. No child agents. Nothing staged or committed.
No shared file edited.

## Status

**CANDIDATE, UNREVIEWED. Not accepted. Do not count.**

`candidate.md` proposes a complete proof of the unchanged I340 target:
for exactly centered, deterministic, grand-canonical hard-sphere fluctuation
fields with $C_c^\infty$ tests, joint convergence in $D([0,T],\mathbb R^m)$
with $J_1$ (indeed C-tightness) on the **whole** supplied regular Boltzmann
lifespan of source H.

## What is new here

- **Lemma W (time-shift averaging).** A redundant contact has no free time
  coordinate. Instead of looking for one, translate every event of the
  connected history by the same $\theta$ and average over
  $\theta\in[0,\tau]$. The translation preserves the chart measure and moves
  the marked time at unit speed. The non-invariant data cost only polynomial
  factors: births use H's displacement-independent $L^1/L^\infty$ bound, each
  link ball becomes a cylinder (losing the link's extra $\varepsilon$ but
  keeping $\mu^{1-h}$), and slab simplices get a factor $(1+a_i)$. H's
  summability is unchanged. This pays the window factor for every C-atom,
  including redundant contacts, which was the unpaid step in I340.
- **Proposition I.** $|\kappa_j(S)|\le C\mu\delta+C_P\varepsilon^P$ for
  two-pulse increments, so
  $\mathbb E|\widehat X_t-\widehat X_s|^4\le C(\delta^2+\delta/\mu)+C_P\varepsilon^P$.
  This replaces I340's qualitative $r_\varepsilon$.
- **Proposition M + Lemma C.** Microscopic modulus at $\alpha=\mu^{-3/2}$ via
  third moments of the number of jumping particles, then dyadic chaining with
  $\theta=1/8$.

Credited from I340 (parent-verified): the continuous Gaussian version and the
exact-centering transfer ($p=22$, rate $\varepsilon^{1/440}$).

## Main risks

1. **Lemma W core (R1)** — whether H's flux-tree and fresh-label counting
   survive the enlargement to formal extended histories.
2. **Lemma E′ (R3)** — the only reading of H beyond its literal statements: a
   final-slab test of root histories, used only for the microscopic modulus.
3. **Novelty** — not checked against the BGSS cumulant papers or elsewhere.

`exclusions-and-failures.md` §3 states the exact missing lemma if either step
is rejected.

## Reviewer checklist

- [ ] R1: Lemma W, Claims 1–3, (W1), §2.5 modifications of H's summation.
- [ ] R2: uniformity of `thm:marked-expansion` remainders in pulse times.
- [ ] R3: Lemma E′ (final-slab root-history test).
- [ ] R4: Gaussian absorption of $\prod_l(1+|u_l|)$.
- [ ] R5: factorial moment–cumulant relations used in Propositions I and M.
- [ ] R6: exponent arithmetic in Lemma C / Proposition M.
- [ ] Contribution review: primary-literature search for whole-history time
      translation averaging in hard-sphere cumulant estimates.

## Files

| File | Content |
|---|---|
| `candidate.md` | Theorem F and full candidate proof |
| `exclusions-and-failures.md` | excluded shortcuts, residual risks, fallback lemmas |
| `reading-and-provenance.md` | source hashes, pinned URLs, exact reading extents, check results |
| `checks/shift_checks.py`, `checks/shift_checks.json` | numerical illustrations (not proof) |
| `provenance.json` | machine-readable hashes and source record |

Source H was reused read-only from `../kinetic-window-discovery/fetched-H/`
after verifying every blob hash against `sources/preprints-tree.json`.
