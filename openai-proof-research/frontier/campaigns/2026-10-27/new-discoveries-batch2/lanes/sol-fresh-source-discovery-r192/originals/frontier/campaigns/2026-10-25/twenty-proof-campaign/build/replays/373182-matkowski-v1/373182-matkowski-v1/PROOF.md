# A continuous nonlinear solution of the Matkowski equation

Define
\[
 f(x)=\min(\max(x,0),1).
\]
Thus f(x)=0 for x≤0, f(x)=x for 0≤x≤1, and f(x)=1 for x≥1.

## Complete counterexample

The function is continuous: maximum and minimum of two continuous real functions are continuous. It is nonnegative everywhere, and for t≥0 it satisfies f(t)≤t.

We prove for every x∈R that
\[
 f(f(-x)+x)=f(-f(x))+f(x).
\]
Since f(x)≥0, the argument −f(x) is nonpositive, so f(−f(x))=0. It suffices to prove that the left side is f(x).

If x≥0, then f(−x)=0, so the left side is f(x). If x<0, then −x>0 and f(−x)≤−x, giving f(−x)+x≤0. The left side is therefore zero; so is f(x). This covers every real x, including zero.

Finally f(1)=f(2)=1. If f(x)=b x throughout the positive half-line, x=1 forces b=1 and x=2 forces 2b=1, a contradiction. Consequently f cannot have any representation
\[
 f(x)=\begin{cases}ax&x\le0,\\bx&x>0,\end{cases}
\]
even without restrictions on a,b. In particular it refutes the more restrictive proposed classification in [MathDB 373182](https://mathdb.com/p/373182).

## Exact prior-art attribution

The primary source is Tibor Kiss, [*A Counterexample to Matkowski's Conjecture for Quasi Graph-Additive Functions*, arXiv:2602.15548v1](https://arxiv.org/html/2602.15548v1). The equation is (1). The proposed classification appears in the introduction and is attributed there to Matkowski's Remark 8/Conjecture 2. Kiss's Proposition 1 and Corollary 1 already yield arbitrary positive-half-line solutions bounded between zero and the identity when the negative-half-line slope is zero. Our function is an explicit instance of that published mechanism. We claim formal verification of this instance, not a new mathematical disproof.

MathDB's exact API snapshot says `open` and has no posted solution, but the cited source explicitly disproves the conjecture. The source-level resolution takes precedence over that database status. The formal counterexample also survives dropping the source's condition a≠b, so it does not exploit that possible wording issue.

## Formal coverage

`MatkowskiCounterexample.continuous_nonlinear_counterexample` asserts, and proves, existence of a continuous real function solving the equation for all real inputs with no two-slope representation. It bundles `cap_continuous`, `cap_equation`, and `cap_not_two_slopes`. Every supporting definition/theorem is printed and audited in `formal/Checks.lean`. The only axiom dependencies are the standard mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`.
