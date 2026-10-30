# Full-target ordinary refutation proposed; credit 0

For the literal integer-radian sum in López Zapata arXiv:2603.14548v2 §6 Conjecture 6.5 / MathDB373621, the ordinary proof and exact rational computation give

    S < 2.163292 < 2.1635 < Ei(log 3).

The finite prefix through 2^30-1 has certified upper bound <2.163159. The WHOLE remaining infinite tail has certified upper bound <0.000134; tighter exact aggregate bounds yield S<2.163292. The right-hand constant has independently certified lower bound >2.163538. No floating-point diagnostic enters any comparison.

The missing remote-tail argument is supplied by the explicit global pi-approximation theorem stated in Boppana2007.11017v1, combined with separated rotation blocks. Finite rational-grid spacing controls dyadic scales 2^30 through 2^1600; the unconditional bound beyond 2^1600 is <2400/2^40. Sparse modular enumeration evaluates only 772779 potentially significant terms past the original10000-term prefix. The optimized exact check took about45 seconds with hard512MiB AS,240CPU/280wall caps and BLAS1.

Read PROOF.md, checks.json, verification.json, constant.json and CERTIFICATE-PLAN.md. Reproduce locally, in this lane:

    python prefix-replay.py
    python check.py
    python constant.py
    python verify.py

The original slow rational attempt also completed successfully; check-slow-attempt.py and check-slow-output.txt preserve it. The optimized pass adds explicit residue-padding assertions and directed fixed-point phase bounds. verify.py rechecks every tail witness and finite residue window/count, prefix replay equality and exact aggregate separator.

**No acceptance or count change.** Strongest objection: this may be a routine correction of a weak numerical guess using classical bounds. Closest-companion full body remains inaccessible (403), complete current-registry/journal clearance is absent, and independent review remains required. A strict Lean certificate has a major missing analytic dependency: the globally explicit Chudnovsky pi inequality has not been located as a kernel theorem. No Lean investment was made, and it must not be hidden as an assumption.

All frozen inputs hash-identical after work (see provenance.json). Only this lane was written. No git, child agents, browser tabs, posting, uploads, contact or account actions. Counts remain5/30 additional,35/60 total; credit0.
