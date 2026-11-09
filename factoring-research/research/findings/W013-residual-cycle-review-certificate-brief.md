# W013 residual-cycle review: preregistered exact certificate (frozen before code)

Fixed exact algebraic checks only. No timing, no performance experiment, no
parameter/depth/prime sweep, no search over N. Inputs are fixed here.

C1. Polynomial identity (P+k*b)^2 - N - b*(a+2kP+k^2 b) == P^2 - N - a*b,
    proved by exact evaluation on a full product grid of 4 points per variable
    (degree <= 2 in each variable; grid vanishing implies identity).
C2. Gower--Wagstaff Table 1 example N=22117019 (=4451*4969, N=3 mod 4).
    Reproduce rows i=0..18 of Table 1 via (2.2)-(2.4). Check: Card update with
    P' = -P + q*Q (sign-corrected) gives the next coefficient; Card's literal
    "P'=P+kb nearest below sqrt(N)" choice gives k=0 and c=a on every reduced
    row; reverse-edge label products are exactly +1 (P'=P) and -1 (P'=-P) mod N;
    product of Card labels equals +/- A_n mod N, where A_n are convergent
    numerators, and A_n^2 - N*B_n^2 = +/-Q_n.
C3. Same N: one full principal period, all signed first-coefficient collisions
    a_i == a_j inside the period. Classify by P_j = +/-P_i mod |a|; compute label
    ratio u mod N, u^2 mod N, gcd(u-1,N), gcd(u+1,N). Check conjugate-type
    collisions give u in {+1,-1,+e,-e}, e = image of the period unit mod N.
    Report all counts; these are descriptive, not performance evidence.
C4. Raw ceil-square recurrence for the same N: 40 steps from a0=1, check
    b == a t^2 - N, b < 2 sqrt(N a) + a (exact integer form), a_i == a0 R_i^2 mod N.
C5. Root multiplicities for the rejection-sampling cost: fixed moduli
    {15, 45, 105, 60, 120, 77}: exhaustive count of square roots per unit square
    (r), formula r = 2^(#odd primes) * c2 (c2=1,2,4 for v2<=1, =2, >=3), and the
    fraction of nontrivial (not +/-1) square roots of 1, 1-2/r.
Any failed check is reported, not hidden; output JSON is hashed in the delivery.
