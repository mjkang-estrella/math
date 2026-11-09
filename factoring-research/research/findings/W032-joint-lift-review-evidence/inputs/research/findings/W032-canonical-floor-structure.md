# W032 continuation: the exact floor left by scalar extraction

Parent derivation, 2026-10-08. No numerical experiment. Verified complete
factoring improvement: **NONE**. The live symbolic audit owns independent
validation of W032; the live assay owns its one frozen finite run.

For R with 2R+1 below the least prime factor, put

    D = 4^R (2R+1)!,
    C_k(a) = D G_k(a^2),
    F(N,a) = sum_(k=0..R) N^(2k) C_k(a).

Every C_k is an integer polynomial: each denominator 4^j(2j+1)!
appearing in G_k divides D. Since D is a unit modulo N, choose the unique
integer h in [0,D) with

    h N^(2R+1) = -F(N,a) mod D.

Then L=(F+h N^(2R+1))/D is an integer and L=V_R(a) modulo N^(2R+1).
L need not be the canonical lift. Subtracting any multiple of N^(2R+1)
changes floor(L/N^(2R)) by a multiple of N, however. Consequently

    d_R(a) = floor(F(N,a)/(D N^(2R)) + hN/D) mod N.       (2)

This formula is exact even when F or L is negative. Use mathematical floor,
not truncation toward zero. It identifies the non-ring operation responsible
for the distinction from the earlier fixed-coefficient screen.

For R=3, the rational diagonal is

    G_1(a^2)=a^2/24,
    G_2(a^2)=3a^4/640-a^2/24,
    G_3(a^2)=5a^6/7168-a^4/192.

With D=322560, define

    B1=13440a^2,
    B2=1512a^4-13440a^2,
    B3=225a^6-1680a^4.

Equation (2) becomes

    d_3(a) = floor((B3+hN+B2/N^2+B1/N^4+D/N^6)/D) mod N,
    h N^7 = -(D+N^2 B1+N^4 B2+N^6 B3) mod D.

This is one exact integer quotient after clearing N^6; its displayed
rationals do not require floating point. B2/N^2 varies by order N^2 on
0<=a<N. Thus even after fixing the small residue data determining h,
the remaining carry is not constant. Treating d_3 as a degree-six
polynomial over F_p would omit this floor. A denominator-residue
partition alone does not repair that omission.

For fixed R this also gives a direct alternative implementation: construct
the bounded-degree integer polynomials, evaluate F by Horner arithmetic,
compute h by a unit inverse modulo D, and take the displayed quotient.
Coefficient generation, log D=O(R log(R+1)), and integer operand widths
must be charged when R grows. A conservative explicit table has O(R^2)
coefficients; the scalar circuit avoids that table. Neither implementation
has a proved useful factor probability. Compact evaluation is the supplied
primitive; generic separating yield is still missing.

## Constructive alternatives within this branch

1. **Remove lower carries exactly.** This returns G_R(a^2) modulo N.
   Its degree is at most 2R in a and its leading coefficient is a unit
   when 2R+1<leastprime(N). Fresh uniform-unit sampling therefore gives
   at most 2R/(p-1) zero probability at p. The carry removal restores a
   simple root bound and cannot be presented as automatic amplification.

2. **Restrict the input interval.** A short interval can make individual
   floor terms simpler, but changes the projected distribution modulo p
   and may remove all separating inputs. The missing claim is a paid
   cover of intervals containing useful roots; no hidden p-dependent
   interval may be supplied to the algorithm.

3. **Retain and analyze the floor.** This is the selected question. Seek
   a separating-count theorem or a counterfamily for the explicit (2),
   with all canonical representatives specified. A random-residue model
   is a hypothesis, not a proof. The finite assay is an implementation
   and identity check, not evidence of an asymptotic exponent.

The exact failed assumption in the earlier public screen was that a small
list of universal numerators covers arbitrary hidden primes. Substitution
and floor extraction change that list to N-dependent tested integers.
Equation (2) states the replacement computation and exposes its remaining
cost and success obligations; it does not resolve those obligations.
