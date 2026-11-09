# Guo Conjecture6.1: full classical bridge, credit HOLD

Primary body: Guo, *Factors of some truncated basic hypergeometric series*, https://arxiv.org/pdf/1901.07908, arXiv v1 (abstract history Jan22 2019 03:40:32 UTC), Section6 p8. Full source statement: for EVERY positive integer n with n=4 or7 mod9,

    S_n(q)=sum_{j=0}^{n-1} (q,q^2,q^6;q^9)_j q^(9j)/(q^9;q^9)_j^3
          =0 mod Phi_n(q)^2.

Here (b;Q)_j=product_{i=0}^{j-1}(1-b Q^i). Congruence means divisibility in rational functions whose denominators are coprime to Phi_n. Since gcd(n,9)=1 and j<n, the displayed denominators are units. No primality of n is assumed. This is one full family, not the q->1 specialization or only n prime. The primary PDF hash is in http.jsonl (b148953b7b0502c5a4e821642381e231d2504140bb987035f09c9db667b16c5f).

## Route1: root evaluation and its first-order obstruction

Let L_b be the least j>=0 with b+9j=0 mod n, for b=1,2,6. A top Pochhammer begins contributing a Phi_n factor at j=L_b+1. In the following table n=9l+s, l>=0:

|s|L_1|L_2|L_6|
|--|--|--|--|
|4|7l+3|5l+2|6l+2|
|7|4l+3|8l+6|6l+4|

Thus terms beyond the second-smallest L vanish modulo Phi_n^2. But the band between the smallest and second-smallest L has only one vanishing top factor. These terms contribute to the derivative at a root of unity. Simply truncating at the first zero or proving S_n(zeta)=0 discards that band and does not prove the square modulus. A direct pairing of only the nonzero head has no justified first-order cancellation. This route identifies a precise missing derivative relation.

## Route2: two terminating deformations close the gap

Work in the localization R=Q[q,q^{-1}]_{(Phi_n)}, and modulo Phi_n^2. Put Q=q^9 and

    f(A)=sum_{j=0}^{n-1} (Aq,q^2/A,q^6;Q)_j Q^j/(Q;Q)_j^3.

This is a Laurent polynomial in A over R, and f(1)=S_n(q). Let delta=q^n-1; it has Phi_n-adic order exactly1. For any fixed integer c, including negative integers,

    f(q^(cn)) = f(1)+c delta f_A'(1) mod Phi_n^2.             (1)

This follows from (1+delta)^c=1+c delta mod delta^2 and polynomial Taylor expansion; no analytic limit is used.

The only classical input is the terminating q-Pfaff–Saalschütz identity, specialized to a balanced product:

    sum_{j=0}^L (Q^(-L),b,c;Q)_j Q^j/(Q;Q)_j^3
       = (Q/b,Q/c;Q)_L / ((Q;Q)_L (Q^(-L);Q)_L),           (2)

when bc=Q^(L+1). More generally the lower parameters are Q,C,bc Q^(1-L)/C; setting C=Q gives (2). This is a finite rational-function identity, valid by continuation wherever denominators are nonzero. The attempted NIST formula access was403 and stopped. A distinct legitimate arXiv primary body was then read: Schilling–Warnaar, arXiv:math/9909044v1 (Sep8 1999), p1, equation(1.1), https://arxiv.org/pdf/math/9909044. Its literal displayed q-Pfaff–Saalschütz formula gives (2) by replacing its base q by Q, its first two top parameters by b,c, its terminating index by L and its lower c by Q. Its second lower parameter becomes bc*Q^(1-L)/Q=Q. The RHS denominator Q/(bc)=Q^(-L). This independently source-checks the exact identity and every specialization; it is not claimed new. Body SHA256 d004c3769c1846b11fc27dbc1ca72971c5129098fb9521915cbc357a2f86d600.

Take t1,t2 from this table:

|n|t1|t2|L1=(t1*n-1)/9|L2=(t2*n-2)/9|J3|J7|J8|
|--|--|--|--|--|--|--|--|
|9l+4|7|5|7l+3|5l+2|3l+1|4l+1|2l|
|9l+7|4|8|4l+3|8l+6|3l+2|l|5l+3|

Here J_b is the least nonnegative j with b+9j=0 mod n. Each table entry is a nonnegative integer; L1,L2<n. The table gives J3,J7<L1 and J3,J8<L2 for every l>=0.

First set A=q^(-t1*n). Then Aq=Q^(-L1), so all terms j>L1 vanish identically. The other top parameters b=q^(2+t1*n), c=q^6 obey bc=q^(8+t1*n)=Q^(L1+1). By (2),

    f(q^(-t1*n))=(q^(7-t1*n),q^3;Q)_L1 /
                     ((Q;Q)_L1 (Q^(-L1);Q)_L1).

The numerator's first factor contains a zero modulo Phi_n at index J7, and the second contains one at J3. The two occur in separate products, so the numerator has Phi_n-adic order at least2 even if their indices agree. Neither denominator contains Phi_n: its exponents are9,18,...,9L1 or -9L1,...,-9, and0<L1<n. Therefore this evaluation is zero modulo Phi_n^2.

Second set A=q^(t2*n). The top q^2/A=Q^(-L2) terminates. Its other parameters b=q^(1+t2*n), c=q^6 obey bc=Q^(L2+1). Thus

    f(q^(t2*n))=(q^(8-t2*n),q^3;Q)_L2 /
                    ((Q;Q)_L2 (Q^(-L2);Q)_L2).

Now J8 and J3 supply the two numerator factors and the denominator is a unit for the same reason. This evaluation also vanishes modulo Phi_n^2.

Applying (1) to both evaluations gives

    f(1)-t1 delta f_A'(1)=0,
    f(1)+t2 delta f_A'(1)=0 mod Phi_n^2.

Their difference is (t1+t2)delta f_A'(1)=12 delta f_A'(1)=0 mod Phi_n^2. The constant12 is invertible in Q and delta/Phi_n is a unit, so delta f_A'(1)=0 mod Phi_n^2. Either equation yields f(1)=0 mod Phi_n^2, the full stated conjecture. All quantifiers, both residue classes, and composite n are retained.

## Limits and classical objection

This is a complete conditional-on-the-standard-identity mathematical derivation, not numerical evidence. It supplies an explicit applicable classical bridge, so shortness alone is not used as an exclusion. Nevertheless the work is a direct application of q-Pfaff–Saalschütz plus first-order interpolation; literature priority and the campaign's substantive-credit threshold remain HOLD. No accepted discovery, manuscript or formal endpoint is proposed. A current exact cited proof or general symmetric-polynomial congruence may already subsume it. The bounded primary/citing search did not establish absence. Root should not count this note merely because the2019 body calls the statement a conjecture.
