# Attempts on the unchanged T024W52 target

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

**Unresolved; no nomination.** The full target is the every-endpoint asymptotic in scope-status.md. The lemmas below are technical support. They use classical prime estimates and averaging, not a new substantial bridge.

## 1. Exact tuple measure and a first attempted route

Fix a large dyadic scale X and form every source parameter from Y=3X. Fix H first. Let nu be the counting measure on distinct totient values in [1,Y], and let mu_H be the pushforward, with multiplicity, of the source basic tuple set T(Y). The actual unique-prefix proposition gives more than cancellation of total cardinalities: outside E* the measures coincide, and both the number of exceptional values and the number of tuples above them are at most

    (epsilon_H + o_{X;H}(1)) Y G_m(Y)/log Y,

where epsilon_H tends to zero. Consequently their signed difference has total variation at most a constant times this quantity. By Ford's scale and the source fixed-dilation theorem, this is at most

    (C epsilon_H + o_{X;H}(1)) V(X).                 (1)

This is a statement about the actual measures, not just their distribution functions.

For y in [X,2X] put h(y)=y/log y and I_y=(y,y+h(y)]. A fixed datum (d,p_1,...,p_R) contributes precisely the primes

    1+y/D < p_0 <= 1+(y+h(y))/D,
    D=d product_{i=1}^R(p_i-1).

The source cofactor-size estimate gives D <= exp((log Y)^0.8). Thus the lower endpoint is X^{1-o(1)}, uniformly in the data, and exceeds Y^0.9. No lower-cutoff error occurs. The classical estimate pi(z)=li(z)+O(z exp(-c sqrt(log z))) gives

    count = (1+o_X(1)) h(y)/(D log X)

uniformly in y and the data, for fixed H. Indeed log(y/D)=log X+O((log X)^0.8), and the endpoint error divided by the proposed main term is O((log X)^2 exp(-c' sqrt(log X))). Summing positive reciprocal weights gives

    mu_H(I_y) = (1+o_{X;H}(1)) h(y) M_1(Y;H)/log X.  (2)

Calibrate the mass by source Proposition mass at t=Y and use fixed dilation V(3X)~3V(X). Since log Y/log X tends to one, (2) differs from h(y)V(X)/X by relative O(epsilon_H)+o_{X;H}(1). The source fixed-dilation conclusion and monotonicity also imply

    sup_{X<=y<=2X} | V(y)/y - V(X)/X | = o(V(X)/X).

For completeness, squeeze y/X between neighboring points of a fixed finite mesh in [1,2]; apply fixed dilation at every mesh point, take X to infinity, then let the mesh size tend to zero. This avoids assuming any continuity of the phase coefficient.

For the discrepancy measure e_H=nu-mu_H, Tonelli gives

    integral_X^{2X} |e_H(I_y)| dy
      <= integral |{y in [X,2X]: y<v<=y+h(y)}| d|e_H|(v)
      <= C X/log X * ||e_H||_TV.

Combine this with (1) and Markov's inequality. For each fixed eta>0, the proportion of endpoints y where |e_H(I_y)|>eta V(X)/log X is at most C epsilon_H/eta+o_{X;H}(1). Equations (1)-(2), then X to infinity and H to infinity, prove convergence in measure of

    [V(y+y/log y)-V(y)] / [V(y)/log y]

to one on [X,2X]. This is an almost-every-endpoint conclusion only. No estimate for the supremum over y follows. It does not prove T024W52 and is not a nominated replacement.

Credits: the entire common-prefix model, uniform small cofactor and exceptional-fiber controls are source-paid. The prime theorem, Tonelli and Markov operations are classical. Ford already gives two-sided order bounds in every much shorter interval (Theorem 4); this argument supplies no new structural input worthy of nomination by itself.

## 2. Why global approximation and local order bounds cannot close route 1

There is an elementary counting-set obstruction, not a counterexample about totients. Start with A_0={n>=1: n mod 4 is 0 or 1}. Choose J_j=2^{2^j}, for j large, and let l_j be the largest multiple of 4 not exceeding J_j/log J_j. In (J_j,J_j+l_j], add all integers congruent to 2 modulo 4. In (J_j+l_j,J_j+2l_j], remove all integers congruent to 1 modulo 4. These disjoint blocks start and end at multiples of 4. Each complete pair changes the count by exactly zero.

At any point t inside a pair, the cumulative discrepancy from A_0 is at most l_j/4. Since t is comparable to J_j, this proves A(t)=t/2+O(t/log t). Outside all pairs the discrepancy is zero, up to the base O(1) rounding. Thus A(t)~t/2 and A(ct)/A(t)->c for every fixed c>0. Every complete four-integer cell contains between one and three elements, so every interval of length h has count between h/4-O(1) and 3h/4+O(1). This includes uniform two-sided order in all intervals of length at least t^0.525.

On (J_j,J_j+l_j] the count is exactly 3l_j/4. Replacing l_j by J_j/log J_j changes the count by O(1). Hence the ratio of this interval count to A(J_j)/log J_j tends to 3/2, not one. On [1,3J_j], the total variation distance from the base counting measure is O(J_j/log J_j)=o(J_j).

Therefore even global asymptotic regularity, small total variation error and uniform short-interval order bounds together do not logically imply the every-window constant-one asymptotic. A local estimate specific to the arithmetic exceptional sets is necessary. This obstruction preserves the full target and says nothing negative about its truth.

## 3. Second route: directly localize collisions

The source comparison proposition bounds ordered shifted-prime factorizations, not just collided values. A useful part of the localization can actually be paid by Ford's classical uniform sieve.

Here is the precise top-layer statement. Retain every hypothesis of source layers.tex Proposition comparison at parameter y, and additionally require the common product to lie in (a/r,b/r], where 0<=a<b<=y and delta=(b-a)/y >=1/(C_0 log y), for a fixed constant C_0. Then its displayed upper bound remains valid with an extra factor delta, after changing the absolute constant to depend on C_0. All lower-layer factors and exponents stay unchanged.

Proof of the changed step: in the source top-layer construction, after fixing sigma_1 and t', write t_1#=t'Q and

    Z=y/(r s_1# t').

The new Q interval has length delta Z and upper endpoint at most Z. If it is nonempty, the source normality/top-product estimate gives Z>=Q>=y^{1/(8 B_y)}, B_y=log log y. In particular delta Z tends to infinity and

    log(delta Z) >= (1/2) log Z >= log y/(16 B_y)

for all sufficiently large y. Translate the interval to the first floor(delta Z)+2 positive integers. The three forms become n+u, A(n+u)+1, A'(n+u)+1 for an integer u. Primitivity, admissibility and determinants are unchanged by translation; the determinant is AA'(A-A'), up to sign. Its magnitude is at most y^3 by the source conditional-coefficient bounds. Ford's actual Theorem 2.5 applies uniformly in all intercepts and coefficients. It bounds the translated count by

    C delta Z B_y^3 / log(delta Z)^3
       <= C' delta Z B_y^6/(log y)^3.

If inadmissible, at most three inputs are possible; the right side tends to infinity uniformly for nonempty configurations, so they are absorbed. The O(1) rounding of interval length is absorbed for the same reason. Summing 1/t' gives exactly the source Euler product factor. Hence the source top-layer inequality gains delta. Every later lower-layer estimate is a positive weighted sum; keeping the new restriction or enlarging it can only decrease these sums. The remaining source proof therefore retains this delta factor. Nothing about the source theorem's truth has been audited or altered.

At first unequal prefix index i=0, this deals with the local collision obstruction directly: impose the full value window at the top comparison and gain its length divided by the ambient value scale. At i>=1, the common largest prime p_0 remains available. Restore it over the interval prescribed by the value window; the source cofactor bound and the quantitative PNT give the same window-length factor. The existing reciprocal suffix sum, tuple recovery and h-index summation are unchanged. Thus the collision portion alone has the appropriate local saving. This is a classical translated-sieve adaptation, explicitly not a substantial nominee.

The source's global i=0 saving alone could not have done this: exp(-c B/m^4) times X/log X does not beat the extra 1/log X needed to obtain o(V(X)/log X) from a global bound. Direct localization, not an unjustified subtraction of global estimates, is what restores the factor.

## 4. Remaining obligation, without a hidden scope change

Coverage and discarded-tuple estimates still require a uniform local proof. In particular source extraction.tex Proposition basic imports Ford's Theorems 10 and 16 for values with some bad preimage. Their displayed contracts are global. They remove all such values before exploiting the largest-prime/cofactor representation. It would be circular simply to apply that good-representation localization to those bad values.

The quantitative obstruction to a naive growing-H repair is explicit. The source uses P=floor(log log H), H<m~constant*log_3 X, and a coverage bound containing exp(-cP). At the maximum allowable size, this displayed bound decays at most on iterated-logarithmic scales, not as 1/log X. An upper bound larger than the desired local scale is not evidence that the actual exceptional count is large; it merely fails to supply the needed estimate. The source repeatedly takes X to infinity with H fixed and only then H to infinity. Its o_{X;H} terms cannot be assigned a useful growing-H rate without additional work.

A sufficient missing bridge is a uniform window version of the finite-map inputs: for every y in [X,2X], coverage exceptions E, discarded tuples D and ordered collision pairs K restricted to I_y satisfy

    |E intersect I_y| + |D over I_y| + K(I_y)
        <= (epsilon_H + o_{X;H}(1)) h(y) G_m(3X)/log X,

with epsilon_H->0 and all parameters frozen at 3X. Section 3 addresses K by a classical operation. No complete local proof for E and D is supplied. Ford's Theorem 4 gives local total counts, not these labeled exceptional subfamilies. Its short-interval statement cannot be silently substituted for them.

Both attempted routes therefore stop at the full every-window target. No narrower theorem replaces it, no contribution gate is claimed, and no acceptance/count change is made.
