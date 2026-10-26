# Weight preservation for Fibonacci recurrences

MathDB 371201. Independently reviewed and verified.

Formal verification of Shivam Patel’s posted orbit-counting proof; no worldwide novelty claim.

Complete proof: [PROOF.md](PROOF.md); paper: [main.tex](main.tex); Lean: [formal/FibonacciWeight.lean](formal/FibonacciWeight.lean).

The release includes `verify_outcome.py` and dependency pins. Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages`. In the campaign checkout use `../../verify_outcome.py`.

See [independent review](review.md), [verification](verification.json), and [audited declaration list](formal/Checks.lean).
