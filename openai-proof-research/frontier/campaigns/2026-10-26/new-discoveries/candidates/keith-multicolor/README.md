# Keith multicolor counterexample — candidate, credit 0

MathDB 345259 / Keith, Restricted k-color partitions II, arXiv:2001.08351v1, Conjecture 1.

For the literal three-color partition polynomial in the 25×25 box at size 325, with the third color variable set to one, the full lattice line y=45−2x has a strict valley. Its coefficients at (20,5),(21,3),(22,1) are 53130, 50600 and at least 52900. This refutes the multicolor extension. It does not refute Dousse–Kim's original two-color conjecture.

The six Lean modules contain 37 declarations. The endpoint source_full_counterexample_345259 concerns the actual generating polynomial summed over mathlib Nat.Partition objects satisfying the literal box restrictions. The partition-count, coefficient and injection bridges are proved, not assumed. No sorry, admit, new axiom, unsafe or native_decide is used. The 2300-witness certificate reduces in Lean's kernel; its compilation can take several minutes and substantial memory (the parent development run used roughly 40–50 GB). Exact resource use varies by compiler/runtime. A fresh strict pinned replay passes all 37 declarations with warnings as errors and only the standard three axioms; its receipt is in verification/audit.json.

Replay from this folder:

```sh
python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

The three-page manuscript and mathematical proof match the finite source refutation. Research notes contain a variable-N family, which is not part of this certificate or a separate discovery count. Independent review, serious bounded novelty investigation, final manuscript gate and extracted proof-packet replay remain required before acceptance. No final proof ZIP is offered yet. Source-access limits are explicit in NOVELTY.md.
