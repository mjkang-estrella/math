# SUPPORTED

The fixed SUPPORTED rule is met: 8 of 10 Test A modules failed at 6 GiB with resource signatures and passed at 32 GiB; all 10 treatments passed. Passing treatment VmPeak exceeded 6 GiB. Only RLIMIT_AS changed for the Lean runs.

Unexpected passing controls: URMatchingCanonical, URMatchingRelabelMaxima. Controls did not mostly pass (2/10).

## Test A

| Module | 6 GiB | 32 GiB | Treatment VmPeak bytes | Treatment peak RSS bytes |
|---|---|---|---:|---:|
| IntervalBlockAlgebra | resource | pass | 6549286912 | 1534447616 |
| ParkingBase | resource | pass | 6796419072 | 1772220416 |
| ParkingCount | resource | pass | 6927319040 | 1884299264 |
| ParkingQuotient | resource | pass | 6801313792 | 1777082368 |
| URMatchingCanonical | pass | pass | 6484492288 | 1484013568 |
| URMatchingRelabelMaxima | pass | pass | 6484426752 | 1479491584 |
| URMatchingStandardGraph | resource | pass | 6585507840 | 1580482560 |
| URMatchingSubgraphMatching | resource | pass | 6584926208 | 1580019712 |
| URMatchingSurvivorCast | resource | pass | 6540664832 | 1536262144 |
| URMatchingSurvivorRatio | resource | pass | 6561992704 | 1552183296 |

All Test A source and olean hashes were unchanged in formal-command records. No Test A module was edited, recompiled or retried. Each Lean command was run once.

## Test B

All three compile runs exited 1 with ordinary elaboration failures; no conditional kernel checks were eligible. Exact diagnostics follow.

NegativeBalanced

~~~text
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/NegativeBalanced.lean:2:61: error: Tactic `decide` proved that the proposition
  (IntervalWidth.balancedBlock 7 3 0).card = 4
is false
~~~

ParkingNegative

~~~text
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/ParkingNegative.lean:6:67: error: unsolved goals
x y : ℚ
⊢ y * x ^ 10 * (1 / 4) + y ^ 4 * x ^ 7 * (-3 / 4) + y ^ 7 * x ^ 4 * (3 / 4) + y ^ 10 * x * (-1 / 4) =
    y * x ^ 10 * (1 / 5) + y ^ 4 * x ^ 7 * (-3 / 5) + y ^ 7 * x ^ 4 * (3 / 5) + y ^ 10 * x * (-1 / 5)
~~~

URMatchingStandardMatching

~~~text
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/URMatchingStandardMatching.lean:25:23: error(lean.unknownIdentifier): Unknown identifier `x`
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/URMatchingStandardMatching.lean:25:33: error(lean.unknownIdentifier): Unknown identifier `x`
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/URMatchingStandardMatching.lean:25:41: error(lean.unknownIdentifier): Unknown identifier `x`
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/URMatchingStandardMatching.lean:26:11: error(lean.unknownIdentifier): Unknown constant `Sym2.mk_right_inj.mp`
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/URMatchingStandardMatching.lean:27:17: error: Type mismatch: After simplification, term
  he
 has type
  s(v, x) ∈ M
but is expected to have type
  (matchingSubgraph hm).Adj v x
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/URMatchingStandardMatching.lean:29:23: error(lean.unknownIdentifier): Unknown identifier `y`
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/URMatchingStandardMatching.lean:29:33: error(lean.unknownIdentifier): Unknown identifier `y`
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/URMatchingStandardMatching.lean:29:73: error(lean.unknownIdentifier): Unknown identifier `y`
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/lean-address-space-diagnostic-sol-r1/src/URMatchingStandardMatching.lean:31:11: error(lean.unknownIdentifier): Unknown constant `Sym2.mk_right_inj.mp`
~~~

## Test C

Complex, Polynomial, Ideal quotients, Real and norm_num: YES, the combined genuine theorem compiled and kernel-checked at 32 GiB address space within the unchanged 6 GiB group RSS guard and 115 s CPU limit. The Complex and Real import names emitted deprecation warnings, but both compilation and checking exited 0; no correction or retry was made.

Full Mathlib: NO. Compilation was killed by the unchanged group RSS guard, before producing an olean. The required subsequent checker invocation exited 1 at the helper assertion "Kernel checker requires actual production olean"; it did not perform a kernel check. No retry.

| Run | Exit | Peak group RSS bytes | VmPeak bytes | Wall seconds | Receipt CPU seconds |
|---|---:|---:|---:|---:|---:|
| c32_compile_ProbeAlgebra | 0 | 2007670784 | 6783295488 | 1.363238 | 1.343776 |
| c32_check_ProbeAlgebra | 0 | 1736433664 | 6767730688 | 1.454389 | 1.366733 |
| c32_compile_ProbeFullMathlib | -9 | 6449565696 | 12334698496 | 3.240400 | 0.018889 |
| c32_check_ProbeFullMathlib | 1 | 12484608 | 251228160 | 0.034443 | 0.034086 |

CPU measurement limitation: for the RSS-killed full-Mathlib compilation, the recorded 0.018889 s covers the reaped Python wrapper only; the killed Lean descendant was not reaped by that wrapper, so total Lean CPU is unavailable. Wall time was 3.240400 s; this was an RSS failure, not a CPU timeout. Successful algebra runs have completed-child CPU measurements (compile 1.343776 s, kernel check 1.366733 s).

The full-Mathlib sampled group RSS peak was 6,449,565,696 bytes (6.0066 GiB), crossing the 6,442,450,944-byte guard. Algebra compile peak RSS was 2,007,670,784 bytes (1.8698 GiB), and kernel-check peak was 1,736,433,664 bytes (1.6172 GiB).

Infrastructure evidence only: credit 0, campaign remains 57 of 80. No candidate becomes green from this test. 323531 excluded with no credit; 338806 on hold; 336276 excluded as routine.
