# Square-uniform Fibonacci minima

[MathDB371202](https://mathdb.com/p/371202) concerns the location of minima in randomly initialized Fibonacci recurrences. The cited source leaves the probability law unspecified. This package proves a complete result for expanding-square uniform sampling: both unique and tie-inclusive minimum-at-zero probabilities tend to5/24, not1/4. It is a qualified interpretation outcome, not a distribution-independent refutation.

The mathematical argument was already posted by Shivam Patel. No discovery or first-formalization claim is made. `main.tex` gives the complete recurrence, cone, counting and limit argument; `formal/FibonacciMinima.lean` proves all of them without supplied bridge assumptions. The source attribution and sampling qualification are recorded prominently throughout.

Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages` in the standalone package, or `python3 verify_outcome.py outcomes/fibonacci-minima` from the campaign. Lean4.34.1 and pinned dependencies in pins.json are required. Third-party full source snapshots are retained in the local source audit rather than redistributed; retrieval hashes and prior reply identifiers accompany the package.

Author Myeongjin Kang. AI-assisted. Original prose CC BY4.0; original code MIT; existing mathematical argument credited to Shivam Patel.
