# discovery.md — pi-discrete-discovery-r7

**Outcome: honest no-result. Zero discoveries counted.**

Targets assigned: MathDB 373197, 372432, 346822, 357859, 346778 (all live-open,
0 solutions at fetch time 2026-10-27).

Per-target disposition:

| MathDB | Question | Disposition |
|---|---|---|
| 346778 | anti-regular graph extremal eigenvalues (Tura) | **EXCLUDED — already resolved**: proved in Tura, Linear Algebra Appl. 612 (2021), DOI 10.1016/j.laa.2020.11.007; independently confirmed by survey arXiv:2610.22838 Theorem 3.8. MathDB record is stale (built on the 2020 2-page preprint). |
| 346822 | Mather polynomials positivity/unimodality/log-concavity | Deprioritized: the record's own source status field quotes the positivity part as "solved" in the source line; the remainder needs heavy Schubert structure-constant data with no small-counterexample lead. Not pursued, no claim. |
| 373197 | Vatter Conj 2.1, principal pattern downsets rank-unimodal | Searched exactly: all perms n ≤ 10 (symmetry-reduced), 150 random 11≤n≤22, 60 layered 11≤n≤21 — all unimodal. No proof attempted (source: "may well be among the hardest to prove"). No result. |
| 372432 | BBK Conj 5.1, G_{k,n}(q) ⪰ 0 for all k,n | Deep investigation (see FINDINGS.md §5): exact reduction G = (q^{2n+3};q²)_{k-2}/(q;q²)_{k-1}; **new structure theorem**: all poles simple ⇒ coefficients eventually exactly periodic with explicit rational mean C = ∏_A j/∏_B j; exact per-coefficient verification for (k ≤ 200, n ≤ 20) ∪ (k ≤ 60, n ≤ 25), zero violations; min coefficient ≥ 1 for k ≥ 2 observed; k=1 tight (zeros). **No uniform proof of tail positivity or of the initial segment ⇒ not counted.** Exact gaps documented. |
| 357859 | Zhang–Zhang Clar covering polynomial unimodality | Open per 2023 source; counterexample search needs benzenoid enumeration (h≈12–13); not pursued in-session; search plan documented. |

Prior-art highlights:
- arXiv:2601.19845 (Chern–Wang 2026) proved the *implied* Andrews–El Bachraoui
  m=1 positivity for all k but does **not** address the G_{k,n} refinement —
  372432 remains open and fresh (bounded screen; two citing bodies unread).
- No other resolution of 373197/357859/372432 found in inspected records.

No PROOF.md, no Lean, no packet: nothing survived to candidate status.
