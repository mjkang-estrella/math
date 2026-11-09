# W014 Card C round 2: preregistered fixed algebra certificate

Written before `certificate_r2.py` was run. It is run exactly once with
`python3 -I`. Exit code, stdout and stderr are retained whatever the result.
This is not a timing run and not a sweep: every input is the fixed constant
listed below. No result here is evidence about asymptotic cost. The checks
illustrate symbolic claims proved in the report. They do not prove them.

Fixed checks (an assertion failure is recorded, not hidden):

- **K1 Cayley images.**
  - Split primes q in {11, 13, 101, 103}, with d a nonzero square s^2.
    a runs over F_q minus {s, -s}, and w=(a+s)/(a-s).
    Predicted image: F_q^* minus {1}, size q-2, uniform (each value hit once).
    With a=0 also removed, the image is F_q^* minus {1,-1}, size q-3.
  - Inert primes p in {7, 11, 103, 107}, with d a nonresidue.
    a runs over F_p, and z=(a+t)/(a-t) lies in F_p[t]/(t^2-d).
    Predicted image: T_{p+1} minus {1}, size p, a bijection.
    With a=0 removed, the image is T minus {1,-1}.
- **K2 Residue images.** For r in {3, 5, 7, 11, 13} and all (a1,c) in F_r^2,
  find the size of the image of x -> a1*x - c/x on F_r^*. Predicted:
  - a1*c != 0: (r + chi(-a1*c))/2;
  - exactly one of a1, c zero: r-1;
  - both zero: 1.
- **K3 Universal identities (Lemma C').** Semiprimes 11*13, 23*47 and
  101*103. For every unit u, check u^f(p,q) == u^F(N), with F(y)=f(1,y), for
  - f in {x+y, x^2+y^2, x^3+y^3, xy+x+y, x+y+(x-1)(y-1)x}.
  Predicted: all hold. f=2x+y with F=2+N must fail for some u.
  Torus: d is the least d>=2 with Jacobi(d,N)=-1, and z comes from
  a=1..20 where valid. Predicted: z^(p-q)==z^(N-1) and
  z^((p-q)^2)==z^((N-1)^2) hold, while z^(p+q)==z^(N+1) fails for some z.
- **K4 Smooth versus bounded order.** Take p=8191 (p+1=2^13), with d=3
  inert. The 8191 Cayley images z, a in F_p, have:
  - orders that are all powers of 2;
  - exactly 63 of order <= 64 (that is, 64-1);
  - exactly 4096 of order 8192.
  Shared annihilation: N=8191*257, d least with (d/8191)=-1 and (d/257)=+1.
  For a=1..30 valid, z^(2^13)==1 globally. Record the step k at which each
  component first becomes 1 under z^(2^k), and whether some k splits N.
- **K5 Coordinate extraction.** N=8191*257, u=3 and z from a=2. For
  j=1..300, hbase^j=(u^j, z^(-j)) with z^(-j)=x+y*t. Compute gcd(u^j-1,N),
  gcd(x-1,N) and gcd(y,N). Predicted: for each prime l of N,
  hbase^j == 1 mod l iff l divides all three. Record every j whose gcds
  are nontrivial.
- **K6 2-D relation.** On the K7 modulus, check
  g'^Dh * hbase^(-(a+b)Dh) == (1, z^(2b Dh)) with g'=g^b*hbase^a,
  for (a,b,Dh) in {(-1,1,3), (2,5,7), (-3,4,11)}.
- **K7 Repaired shared-slope 2-D schedule on one fixed instance.**
  - Instance: N=10007*7919, u=2, cayley a=2, d least with Jacobi -1.
    X=isqrt(N)+1, L=1200, H=100 (12 blocks), common slope (a,b)=(-1,1),
    c0_i=round(N/X_i), E_i the exact ceil of max over the block of
    |N/(X_i+h)-c0_i+h|, H1=10, B=16.
  - Both role assignments are run.
  - Report babies, giants, duplicate baby keys, matches, divisibility tests
    and the found factor.
  - Predicted:
    - giants == sum_i ceil(H/H1)*ceil((2E_i+1)/B) per role;
    - the true P=10007 is found in exactly one role;
    - no duplicate baby keys.
  - Literal 1-D schedule on the same blocks, with B1=max_i(2E_i+1):
    giants == L per role, and the true pair matches.
