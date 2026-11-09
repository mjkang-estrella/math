# W021 block-product certificate: preregistration (frozen before execution)

Purpose: a toy exact-algebra certificate for W021 section A. It checks the block
identity, the post-construction digit relabelling, shifted intervals, the
incomplete tail, signed and very wide exponents, composite moduli with repeated
points and zero factors, against independent direct products. It does NOT
implement Kedlaya--Umans or van der Hoeven--Lecerf evaluation (the relabelled
polynomial is evaluated by plain Horner), and it establishes no asymptotic bound.

Script: `certificate.py` (stdlib only; run once with `python3 -I`).
Hashes of this file and the script are recorded in `certificate-freeze.json`
before the single execution. Results go to `certificate-results.json` and
the console log to `certificate-run.log`. No tuning, sweeps, or reruns. Any
failure is retained and reported.

## Budget
Total wall time <= 60 s (checked at the end; a cooperative check aborts a case
if exceeded). Charged events <= 20000 over all cases: each modular
multiplication, modular inverse, and modular addition inside the candidate path
counts one event. The direct reference uses Python `pow(alpha, e, N)` per leaf
and is metered separately (one event per leaf plus per-leaf multiplication);
both meters share the 20000 cap. Exceeding the cap aborts and records failure.

## Candidate path (per case)
1. Exponent setup by finite differences only (one binary powering of each of
   alpha^(A+D), alpha^(2A), alpha^(2Ab), alpha^(2Ab^2), alpha^(Ab^2+Db),
   alpha^C; negative exponents via one checked inverse of alpha).
2. c_j = alpha^(A j^2 + D j), 0<=j<b, by first/second differences.
3. F(X,Y) = prod_j (1 - c_j X^j Y) by a balanced product tree of dense
   bivariate arrays (schoolbook multiplication). Record actual X/Y degrees
   and per-level dense slot counts.
4. Relabel AFTER construction: X^e Y^h -> X0^(e mod b) X1^(e div b) Y^h.
   Check all three partial degrees <= b.
5. Points X_k, X_k^b (as alpha^(2Ab^2 k), computed independently by its own
   geometric sequence), Y_k by second differences, k < floor(L/b).
6. Evaluate G at (X_k, X_k^b, Y_k) by Horner; also evaluate F directly at
   (X_k, Y_k) as a cross-check.
7. Tail leaves (fewer than b) via the same finite-difference recursion.
8. Product of block values and tail.

## Comparisons (all must be exact equalities modulo N)
- C1 block value G(X_k,X_k^b,Y_k) == F(X_k,Y_k) == prod_j (1 - pow(alpha,f(bk+j),N)).
- C2 total candidate product == direct product over all leaves.
- C3 deg_X F <= b(b-1)/2, deg_Y F <= b, relabelled degrees <= (b-1, (b-1)//2, b).
- C4 shift case: candidate with (D+2Aa, C+Da+Aa^2) on [0,ell) == direct
  product over original indices [a, a+ell).
- Negative control N1 (expected NOT equal as polynomials): relabelling applied
  to factors before multiplication, i.e. product of psi(factor_j), has an X0
  degree exceeding b-1 for some case with b>=3, so psi is not a ring
  homomorphism on the construction; its evaluation at (X, X^b, Y) still agrees
  numerically (recorded, not a pass criterion).

## Frozen cases
| id | N | alpha | A | D | C | L | b | note |
|----|---|-------|---|---|---|---|---|------|
| K1 | 15 | 2 | 1 | 0 | 0 | 7 | 2 | f(0)=0: zero factor, odd tail |
| K2 | 91 | 3 | 5 | -7 | -11 | 23 | 3 | signed exponents, tail 2 |
| K3 | 1001 | 10 | -3 | 4 | 2^70+5 | 20 | 4 | wide C, exact blocks |
| K4 | 45 | 2 | 6 | 12 | 0 | 17 | 3 | non-prime-power-free N, repeated points |
| K5 | 221 | 220 | 1 | 1 | 1 | 12 | 3 | alpha=-1: all points repeat |
| K6 | 1155 | 2 | -(2^64+3) | 2^40 | -(2^90) | 10 | 2 | huge negative widths |
| K7 | 35 | 3 | 2 | 1 | 0 | 2 | 3 | L<b: tail only |
| S1 | 91 | 3 | 5 | -7 | -11 | ell=11, a=9 | 3 | shifted interval vs original indices |

Success: every C1--C4 comparison is equal in every case, within budget.
Any mismatch, exception, or budget overrun is a recorded failure.
