# H003: exact local filtering leaves a large explicit global set

Status: mathematical derivation and finite checks complete; independent review
pending. This is a narrow cost gate for a known sieve, not a new factoring result.

## Candidate and prior-art disposition

The proposed route filters candidate sums s = p + q by requiring s² − 4N to be
a quadratic residue or zero modulo small odd primes. The candidate's tempting
step is to equate compact local constraints with cheap recovery of a useful
global s. The hyperbolic/factor-sum sieve and subset-sum formulation are already
studied by [Hittmeir](https://arxiv.org/abs/2205.10074). This baseline is known,
so a novelty claim would require a new costed global-query primitive.

## Elementary derivation to review

Fix an odd prime ell not dividing N and let R_ell contain the allowed s residues.
Count pairs (s,y) satisfying y² = s² − 4N over F_ell. Since 2 is invertible, the
change of variables u=s−y, v=s+y bijects these pairs with uv=4N. The latter has
ell−1 solutions, one for each nonzero u. Exactly z=1+chi_ell(N) of the solutions
have y=0, because s²=4N. Every allowed s with nonzero y contributes two pairs;
an allowed s with y=0 contributes one. Consequently:

```
2 |R_ell| − z = ell − 1,
|R_ell| = (ell + chi_ell(N))/2.
```

For k distinct odd primes with product M coprime to N, CRT gives exactly
|R_M| = product |R_ell| residues. Each local fraction is at least 1/3, so
|R_M| >= M/3^k. Order the primes ell_i increasingly. Since ell_i >= i+2,
M >= (k+2)!/2. Thus k/log(M) → 0 as M → infinity across any such choices:
if k stays bounded the claim is immediate; for large k, the largest floor(k/2)
factors are at least k/2, giving log M >= floor(k/2) log(k/2).
It follows that log(|R_M|)/log(M) → 1, using |R_M| <= M for the upper bound.

Materializing the complete set therefore costs at least M^(1−o(1)) output items.
If M is chosen on the scale N^theta for fixed theta>0, this alone gives no fixed
power reduction below N^theta in full-set output size. This is compatible with
subpolynomial density improvements and does not negate known sieve improvements.

Scope is crucial: this is not a lower bound on a short interval's intersection,
the cost of a compact representation, subset-sum algorithms, or factoring in
general. The unresolved possibility is computing useful interval intersections
without enumerating the full CRT set. Requiring s even can be encoded by an
additional modulus 2; its constant density factor does not change this conclusion.
Prime powers, correlated extra equations, and non-CRT representations are outside
this derivation. A prime dividing N already supplies an ordinary factor and is
excluded from the cardinality statement.

## Reproducible finite evidence

Protocol: research/hypotheses/H003.md. Executed:

```
timeout 60s .venv/bin/python research/experiments/H003/sieve_cardinality.py
```

The run checked 266 local identities (every nonzero residue for odd primes <=43),
12 explicit CRT stages for two declared N values through modulus 255255, and
direct-set equality for all stages through modulus 15015. Seven counts-only rows
through 64 primes verify numerical bounds without pretending to enumerate the
large sets. The run took about 0.01 seconds. Raw output includes the source hash:
research/experiments/H003/result.json. The script refuses to overwrite evidence.

These finite checks catch implementation/identity errors but are not the proof
of the asymptotic statement. No Lean finite-field formalization was added because
this known-method rejection gate does not justify new algebra infrastructure.

## Next decisive action

Independent reviewer: check the pair count, the sequence-uniform asymptotic step,
and the exact limit of the claimed obstruction. Then identify whether a *specific*
structured multiple-choice subset-sum / interval-query algorithm could bypass
materialization at a cost competitive with appropriate known factoring methods.
Do not replace that missing primitive by a free oracle or conclude that no such
primitive exists. Current verified algorithmic improvement is NONE.
