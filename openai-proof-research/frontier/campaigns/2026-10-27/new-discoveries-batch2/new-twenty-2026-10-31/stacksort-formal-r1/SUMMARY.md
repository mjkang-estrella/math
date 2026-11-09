# Formalization round 1 — partial, not accepted

The source-reading refutation is NOT closed. Its three endpoints compile with exactly two explicit hypotheses, `StackSort.Doubling` and `StackSort.Lower130`. They are ordinary `Prop` definitions, not added assumptions in the environment. No credit is claimed; root decides.

Completed: literal max-split map on lists, permutation-word domain, cardinality n!, preservation of that domain, source split equation, order-equivariance, literal pair count, average and squared-fibre identities, the series-free dyadic iteration, analytic subsequence/limit wrap-up, and a kernel-checked integer inequality at base 130. The subsequence has `index 130 k + 1 = 131 * 2^k`.

The maximum-fibre reading IS closed unconditionally, including its companion for every n ≥ 5. The explicit family of identity preimages has cardinality 2^(n−1). This reading earns no credit by itself.

Open: L3 doubling injection and factorial conversion; L6 root-split injection and verified lower-table linkage; L7 correctness of the top-max recursion and exact seeds through 20. `RootSplit`, `DoublingInjection`, `ExactSeeds20`, `Doubling`, and `Lower130` are exact Lean propositions in StackSortFinal.lean. Standardisation is proved. The literal lower130 constant has a proved integer certificate, but identifying it as a lower bound on P 130 is explicitly unproved. Python agreement is diagnostic only.

Small literal kernel counts are checked through P 4 = 224. The attempted direct P 5/P 6 combined check failed under -M3500; P 5 alone also hit the kernel memory limit. Neither P 5 nor P 6 is claimed as a completed Lean regression. Python literal counts through 8 and an independent full, unpruned top-max computation through 20 match the cached exact table. No P 50 or P 78 was evaluated in Lean.

Resource exception: an incorrect `leanchecker --help` probe scanned all modules and reached 12,694,900 KiB peak RSS before termination. It exceeded the required RSS bound; the run is not claimed fully resource-compliant. All subsequent calls use a process RSS watchdog at 6 GiB in addition to taskset, CPU/wall limits, MALLOC_ARENA_MAX=2 and -M3500 on Lean. The initial 6 GiB virtual-address cap prevented reading mapped imports; it was removed because virtual address space is not RSS. No background process is intentionally retained.

See results.json for final validation status and totals; REPRODUCE.md for replay commands. All files are in the assigned lane. No git, network, browser, upload, publication, external message, child agent, shared-ledger edit, or intentional out-of-lane write was used.

Validation before packaging: strict serial compilation and leanchecker pass for all 11 modules (10 proof/definition modules plus the audit module). The endpoint import closure contains 348,450 kernel declarations from 3,530 modules, including 110 local declarations; the audited set equals that closure exactly. Local metadata flags are all zero. All five endpoint dependency traversals have exactly the permitted axioms. The 344,389 compiler extra symbol names are inventoried separately; 900 also identify kernel declarations. Upstream metadata is reported separately in audit-summary.json. Four Lean negative-control theorems reject a wrong seed, base 129, threshold 1.95, and the wrong convention.
