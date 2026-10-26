# A finite additive-count counterexample

[MathDB 334772](https://mathdb.com/p/334772) states an unrestricted monotonicity assertion for the number of functions satisfying a k-summand additive relation. For E={1}, let S contain the identity and the function equal to the identity except at 2, where it is zero. The counts are exactly 1 at k=2 and 2 at k=3. The complete cardinality and universal relation proof is in Lean.

This is an elementary correction to the literal MathDB wording. The cited [Park manuscript v1](https://arxiv.org/abs/1612.00897v1) was read in full and does not contain the stated general conjecture. No conjecture is attributed to Park here, and no claim is made about a version restricted to multiplicative functions or other input sets. No worldwide novelty claim is made.

Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages` in the standalone package. In the campaign, run `python3 verify_outcome.py outcomes/additive-monotonicity`. Lean 4.34.1 and the dependencies pinned in pins.json are required. `main.tex` gives the full written argument; `COVERAGE.md` maps it to the formal development. The source provenance and eventual independent review accompany the package.

Author: Myeongjin Kang. AI-assisted. Original prose CC BY 4.0; original code MIT.
