# progress log — pi-karp-full-sign-r1

All times UTC, 2026-10-28.

1. 17:17 — Read ancestor `openai-proof-research/AGENTS.md`, batch
   `new-discoveries-batch2/AGENTS.md`, batch `ledger.json` (2/30 additional, 32/60 total),
   `prior-campaign-context.json`.
2. 17:20 — Read prior root lanes: `root-beta-convolution-r9/PARTIAL.md` (+ `check_partial.py`,
   `checks.json`, `sources/karp-beta-v1.html`, sha256 282bcf…47cb56),
   `root-beta-convolution-r17/PARTIAL.md` (+ `check_structure.py`, `screen.py`,
   `screen.json`, `exact-structure.json`), and `root-special-screen-r6`
   (`FINDINGS.md`, `post-331384.json`, `karp-beta.html`). No prior lane rejection notes for
   this target beyond the documented partial-status limits.
3. 17:25 — Read the actual primary source end to end from the retained cache
   (`karp-beta-v1.html`, arXiv:1509.05120v1): Eq.(1), Eq.(6), Lemma 1 (+proof), Theorem 2,
   Conjectures 1–2, Lemma 2, Theorem 3, Corollary 1 (+proof, incl. Bustoz–Ismail [5,
   Theorem 6] step), Theorems 4, Corollaries 2–6, full reference list. Confirmed: negative
   half and integer-shift case are proved in-source; full `b>1` arbitrary-shift case is the
   open content; no `k!` weighting anywhere in the psi definition.
4. 17:17–17:35 — Early prior-art/followup screen (web search, 3 query angles): located the
   trureturing public registry ("Discovering truth", the-omega-institute). Conjecture 1
   recorded PROVED (D5/S3/Analytic/IncompleteBeta); its page explicitly states "OPEN.
   Conjecture 2 … is not addressed here." A dedicated Conjecture 2 problem page
   (`karp-2016-incomplete-beta-first-parameter-coefficient-signs`) is triaged PROVED for all
   real parameters and all natural n, both branches.
5. 17:40 — Fetched and read the actual Lean bodies at pinned commit 337295b:
   `IncompleteBetaShape/Defs.lean` (`psi`, `claim` — literal Conjecture 2),
   `IncompleteBeta/Defs.lean` (`coeff` = h_b(t+j), no k!), `Result.lean` (result theorem,
   0 sorry/admit/axiom/native_decide), `Mixture.lean`, `Kernel.lean`,
   `IncompleteBeta/Comparison.lean` (0 sorry each), and the frozen-state record
   `Golden/Frozen/state/.../Result.lean.json` listing all five module theorems.
6. 17:50 — Independently re-derived the mathematical route by hand (affine mixture identity
   via the (v,s)->(x,z) change of variables; kernel monotonicity via
   r(1-r)-l(1-l)=s(1-s)(1-2v); constant K=(n+1)Gamma(c+n+2b)/(Gamma(b)^2 Gamma(c+n+2)),
   hand-checked at b=2,n=0). Matches the Lean development exactly. See discovery.md.
7. 18:05 onwards — Built `verify_route_chain.py` (final: 30 dps, 70-node tanh-sinh rule
   per integral, exact `1-x` carried per node, betainc-based inner integral; <512MiB).
   Debugging history retained for honesty: an initial adaptive-mp.quad version agreed to
   3.7e-38 on one b=3 case but exceeded memory on extreme shapes; a first Gauss-Legendre
   version failed on endpoint-singular weights; a tanh-sinh version initially mis-signed
   the deep-node transform (x=(1+tanh sh)/2 instead of 1/(1+e^{-2sh})) and suffered
   40-dps rounding of x near 1 — both fixed and root-caused. Final saved result
   (`verify_route_chain.json`): 8/8 route identities agree to rel <= 4.5e-8, 8/8 sign
   branches match. Beta shapes < 0.1 excluded (mean concentrates below reachable
   quadrature depth; the Lean proof is analytic there).
8. 18:10 — Retrieved commit metadata (commit dated 2026-10-28T16:10:44Z, merge PR #23195);
   saved all sources with sha256 in this lane's `sources/`; wrote provenance.json.
9. 18:12 — Decision: target publicly resolved; no formalization, no manuscript, no review,
   no packet; credit 0. Wrote SUMMARY.md and this log. No external actions performed; no
   edits outside this lane; MathDB record untouched.

Falsifiers attempted and retired (documented so they are not retried):
- Pairing argument on `r_S'` (fails: r' not monotone in distance from S/2; concrete h_3,
  S=10 counterexample to the sufficient condition).
- Generic log-concavity of h (refuted by r17's exact h=t^2 instance).
- Induction b -> b+1 via (t+b)h_b(t)=b h_{b+1}(t) (introduces index-dependent weights;
  no clean decomposition found; superseded by the public mixture route).
