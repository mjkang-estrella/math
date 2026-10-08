# H030 C2 admission review — raw, NOT accepted wholesale

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h030-coefficient-trace-admission-opus-20261008-r1`
Completed 2026-10-08, claudeAgent / claude-opus-5-5. Root reconciliation pending. Unmeasured timing, feasibility, statistical-power and implementation claims below are not established facts.

I've finished reading the files and am writing up the review now.

# H030 C2 admission review: execution should stay parked

I made no edits, ran nothing, and started no child tasks. I read `RESEARCH_TEAM.md`, `RESEARCH_LOOP.md`, the H030 part of `STATE.md`, and the five H030 records you listed.

## Decision

**Do not admit a numerical test now. Keep C2 as a paper candidate and park execution.**

- There is a real mechanism: partial steps skip both M and S.
- But no setup that fits the 60 s / 1M-event bound can change the conclusion:
  - At sizes that fit the budget, the complete-work outcome is already fixed by setup costs.
  - The per-step operation counts can be worked out exactly on paper.
  - The deciding parameter can't be measured in this project.

## Paper ledger per logical step

This is the regular case with batched inversion, against competent negation rho using a canonical y.

| | Baseline (r_B large, e.g. ≥512) | C2 at (r, τ) |
|---|---|---|
| Arithmetic | 5M+S+6A+(I−3M)/n | (4+1/τ)M + S/τ + (4+4/τ)A + (I−3M)/n |
| Canonicalization | canon(y) once | canon(H) once (same cost) |
| Field-element transfers | 6: jump 2, state in 2, state out 2 | 8+3/τ: K′ record (x,y,h) 3, origin (x₀,y₀,h₀) 3, H in 1, H out 1, refresh write 3/τ |
| Index work | jump address from bits of y | K-index state plus a data-dependent read from a pointer table of size 2r·N(r,τ−1) |
| 2-cycle reduction (random-index heuristic) | ≈1/r_B, negligible | ≈(1/r)·one extra partial step ≈ 4M/r |

Notes on the ledger:
- **Arithmetic credit:** (1−1/τ)(M+S) + (2−4/τ)A. With S=0.8M and A=0 this is 0.9M at τ=2 and 1.2M at τ=3.
- **Ceiling:** as τ→∞ the credit approaches about 31% of a step (about 1.45×). At feasible τ≤3 it is at most about 1.2×, before any extra costs.
- **Data-structure sizes (256-bit field):**

| (r, τ) | Folded records | Record bytes | Pointers | Where it fits |
|---|---|---|---|---|
| r=16, τ=2 | 272 | 26 KB | 1,056 | L1 |
| r=32, τ=2 | 1,057 | 101 KB | — | — |
| r=16, τ=3 | 3,008 | 289 KB | 17,440 | L2 |
| r=16, τ=4 | — | 2.4 MB | — | L3 |

C2 is effectively limited to r≈16–32 with τ≤3. The comparator is not limited this way.

## Symbolic break-even

Let w be the cost of one field-element transfer as a fraction of M, ℓ the cost of a pointer read, δ the walk-law penalty of C2's h-walk at r against the baseline at r_B, and Δcyc the cost of cycle, escape, report, zero-H and false-H-repeat events. C2 gains only if:

(1−1/τ)(M+S) + (2−4/τ)A − 4M/r > (2+3/τ)·w·M + ℓ + δ·(5M+S+6A) + Δcyc + setup/steps

With ℓ, δ and Δcyc all set to zero, the largest w that still breaks even is:

| (r, τ) | w must be below | Headroom at w=0 |
|---|---|---|
| r=16, τ=2 | 0.19 | 11% |
| r=32, τ=2 | 0.22 | 13% |
| r=16, τ=3 | 0.32 (0.36 if S=M) | 16% |

Each 1% of δ uses up about 0.058M of headroom.

The three cost layers give different answers:
1. **Operation-vector counts (w=0):** positive, 11–16%.
2. **A named 4-limb Montgomery word-operation model:** w≈0.05–0.07, so still positive, about 12–14%.
3. **Equal-unit pricing (one word read = one M):** negative at every feasible τ, because the credit stays below 1.8M while Δtransfers ≥ 2.

So the verdict is decided by real memory cost at the target field size. This is a timing question on a platform, not something an operation count can settle.

## Why no bounded test changes the conclusion

- **Complete-work test at admissible sizes: the result is known in advance.** C2's setup is about 272 records × ~6M plus the paid Miller bootstrap, roughly 2.6k M even at r=16, τ=2. At w=0, setup breaks even only once 0.886√q·0.65M exceeds that, i.e. q ≳ 2²⁴. Sizes that fit the budget therefore sit at or below break-even because of setup alone, and r=16, τ=3 pushes break-even to q≳2²⁸. A loss there would be an artifact of size, not a falsification.
- **Per-step arithmetic is already exact on paper.** τ does not change the logical walk.
- **The only C2-specific unknown that can be measured is the walk law.** That means the h-oriented walk's steps per useful collision and its event rates, compared with the y-oriented walk.
  - Steps-to-collision vary a lot from run to run (CV ≈ 0.52). Within 1M events, a test could only detect anomalies of about 12% or more, which is roughly the w=0 headroom.
  - There is no algebraic reason to expect an anomaly. Both arms take index and sign from one canonical field element.
  - If the test passes, C2 is still parked on w. Only a kill would change anything, and its prior probability is low.
- **Timing synthetic one-word fields measures the wrong ratio.** Single-word fields make M artificially cheap compared with memory traffic.
- **A full-coordinate equivalence check removes no open blocker.** Root and Sol already checked the logical successor and the exception dispatch independently.

I did not extend this to the μ6 case. It would make the table larger and add cost, and it cannot fix the w premise.

## Missing premise

For a named field size and platform, there needs to be a justified per-step cost for the extra 2+3/τ field-element transfers from a data-dependent table (26 KB at r=16, τ=2; 289 KB at r=16, τ=3), plus the pointer read. That cost must come in below the bounds above, with the leftover margin still covering δ for r=16 against the comparator's own r.

Synthetic runs in this project cannot supply it. A primary-source implementation measurement, or a reviewed 256-bit cost model for loads versus multiplications, could.

## Recommendation

Record C2 as **"valid constant-factor arithmetic mechanism; execution parked on the memory-cost premise w."** The 11–16% operation-count headroom is a conditional ceiling, not a solver gain. There is no novelty claim, the Bos/BLS prior art stands, and verified complete-work improvement is still NONE.

If someone later supplies the premise, the admissible test becomes a τ-free walk-law comparison under the bounds already set:
- **Arms:** the h-walk at r=16, the y-walk at r=16, and the y-walk at the comparator's own r.
- **Shared across arms:** identical jumps, the same 2-cycle rule, and the same DP detection.
- **Sizes and seeds:** increasing q, full-range uniform seeds, and no structured k=q/3.
- **Counted events:** h=0 fallbacks, false-H-repeat verifications and escapes.
- **Kill rule:** kill C2 if its δ exceeds the headroom that remains under the supplied w.
