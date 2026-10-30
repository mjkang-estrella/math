# MathDB 371202: square-uniform interpretation

**Result:** For the actual bi-infinite integer Fibonacci recurrence, initialized uniformly on `[-N,N]^2 ∩ ℤ²`, the probability of an absolute minimum at zero tends to `5/24`, for both a unique minimum and ties allowed. The complete recurrence, global-event characterization, actual finite count, and limit are formalized in one Lean module with no missing-bridge hypotheses.

**Critical source qualification:** Pudelko's arXiv:2510.24882v2, Conjecture 20 / equation (20), specifies random integer initialization but does **not** specify expanding-square sampling. This is a counterexample to that precise interpretation; it is not a distribution-independent refutation of the underspecified source. Patel's existing reply incorrectly describes square sampling as explicitly source-specified. The present record corrects that attribution and preserves the mathematical argument.

**Credit:** The cone/count/`5/24` counterexample is due to Shivam Patel, MathDB reply UUID `009c10c4-3dc7-47ce-8c70-0b9ae15e58a3`, posted 2026-08-20. No mathematical novelty claim is made. The full tie-inclusive finite bound and formal bridges are supplied here as verification work. MathDB 371201 is a separate already-counted recurrence-weight outcome and is not counted again.

## Exact definitions and proof

The integer-indexed sequence `sequence x y` joins recursively defined forward and backward tails. They have initial values `x,y` and `x,y-x`, respectively, with forward rule `u[n+2]=u[n]+u[n+1]` and backward rule `b[n+2]=b[n]-b[n+1]`. `sequence_recurrence` proves the required Fibonacci equation for every integer index.

`global_minimum_iff` proves that `minimumAtZero` means the unique global absolute minimum of this sequence, not a local event. `minimum_iff_cone` proves its exact characterization:

- `x=0` and `y≠0`;
- `x>0` and (`y<-2x` or `y>3x`);
- `x<0` and (`y>-2x` or `y<3x`).

Necessity uses positions `1,2,-1,-2`. Sufficiency covers both infinite tails by induction on the recurrence: forward same-sign tails grow beyond the threshold; backward opposite-sign tails alternate and grow in absolute value. Simultaneous negation treats negative `x`.

The finite sample `square N` is the product of the actual integer intervals `[-N,N]`, with card `(2N+1)^2`. `successes N` filters this sample by the global minimum predicate. `count_rows`, `row_positive`, `row_zero`, and `symmetric_sum` establish

`card(successes N) = 2N + 2 triangle(N,2) + 2 triangle(N,3)`,

where `triangle(N,k)=Σ(j=1..N) max(N-kj,0)`. A positive row `x=j` consists of disjoint integer intervals `[-N,-2j-1]` and `[3j+1,N]`; simultaneous negation counts the negative rows. Thus no count-to-event bridge is assumed.

For `k>0`, the sum truncates at `q=N/k` (natural division), and `triangle_formula` proves

`2 triangle(N,k)=q(2N-k(q+1))`.

The remainder in `N=kq+r`, `0≤r<k`, gives `q/N→1/k`; normalized triangle counts tend to `1/(2k)`. Hence the total success count divided by `N²` tends to `5/6`, while the sample card divided by `N²` tends to `4`. `square_uniform_limit` proves the probability limit `5/24`.

For ties, `weak_global_minimum_iff` identifies the weak global event. `weak_strict_or_boundary` proves every non-strict weak minimum lies on `y=-2x` or `y=3x`. Each line has at most `2N+1` square points (inject into its first coordinate). Consequently the weak count differs by at most `2(2N+1)`, and `weak_square_uniform_limit` obtains the same `5/24` limit by squeezing. Any valid deterministic tie-assignment rule lies between these strict and weak events, so the tie convention cannot restore `1/4`.

The main theorem `FibonacciMinima.fibonacci_minima_square_counterexample` packages the recurrence, global cone criterion, exact square count, both limits, and exclusion of a tie-inclusive limit of `1/4`. All statements are hypothesis-free except parameters appearing in the corresponding elementary/general lemmas.

## Formal coverage and limits

The theorem applies to the standard Fibonacci recurrence on all integer indices. A counterexample for this recurrence suffices against a formula claiming to include it; no independent chiral-recurrence proof is claimed. No result for the probabilities at other indices, the full Lucas-ratio expression, or a rotationally invariant law is claimed.

The source does not define a unique probability law. This record must be counted, if at all, with the explicit qualification “square-uniform interpretation”; it cannot honestly be described as an unconditional resolution of the original underspecified conjecture. Parent independent review will decide campaign eligibility.

## Verification

Run from the repository workspace:

```bash
python openai-proof-research/frontier/campaigns/2026-10-25/twenty-proof-campaign/verify_outcome.py openai-proof-research/frontier/campaigns/2026-10-25/extension-fibonacci-minima
```

The pinned audit passed under Lean 4.34.1 with warning-as-error compilation of the source and all-declaration audit. It checks 48 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`. See `build/audit.json` for the exact final source hash. No proof placeholders, extra postulates, or trust-expanding evaluation mechanisms occur in the source. The current paper source is `main.tex`; PDF rendering is assigned centrally to the parent.
