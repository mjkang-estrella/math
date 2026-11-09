# W006 — fixed primality-certificate and folded-vector check

Frozen 2026-10-08 before this execution. One run only. Exclusive prefix
research/findings/W006-cyclotomic-validation-, report
research/findings/W006-cyclotomic-validation.md. Standard library only.

Fixed target integers: 1610612737 and 3221225473.
Fixed bases per target: 2,3,5,7,11. Test in that order and stop after the
first valid prime certificate. No replacement targets or search.
Check t=3*2^e+1 for the stated e=29,30 and (2^e)^2>t exactly.
For each base check its gcd and a^((t-1)//2) mod t by explicit binary
modular powering, recording every multiplication and maximum operand width.
A residue t-1, together with the algebraic hypotheses and checked unit base,
is a certificate only after the symbolic proof has been validated.

If BOTH certificates verify, form N=p*q and compute cyclic coefficient
vectors for L=2,4,8,16 exactly as W006 A. Record every coefficient and gcd;
all-unit output should follow from the proposed theorem. If either target
has no certificate, record UNKNOWN for the combined theorem instance and
do not improvise a primality method or target search. Any computed proper
gcd is retained and checked. The candidate receives only N,L.

Budgets: 60 seconds whole run including setup, 1 second per target/degree
case, 20,000 recorded modular multiply-adds per case, soft 32 MiB traced
allocation, 1 MiB per-case and 16 MiB overall evidence. UNKNOWN all censored
and unstarted cases. No reruns, no exact central coefficient of this huge N,
no expanded degree/base menu. Freeze source, protocol, exact inputs and
hashes before execution. This is a certificate check and primitive failure
instance, not a factoring performance comparison. Run scripts/check.sh
after scratch code, outside this screen budget.
