# A common dense set with two disjoint denominator valuations

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

This is an author proof module, conditional on the exact source025 divisor-moment and reciprocal-phase lemmas. The modified random-product estimate is proved below from the actual source proof, not asserted by changing its quantifiers.

## 1. Parameters and statement

Use the source constants K=100, R=1000, D0=100000, eta=10^-4, DM=(2R+2)(K+2), DX=DM+2, DC=4DX. Let S be sufficiently large and C an odd integer with

    exp(1.4 DC S) <= C <= exp(1.6 DC S).

Put m=floor(S/log S), rho=exp(-eta m), X_j=exp(DX S)rho^j, d=min{j:X_j<=exp(m)}, and C_j=C when X_j>exp(S), otherwise C_j=1. These are the original levels. In particular d<=Kd log S, Kd=3DX/eta, X_d>exp((1-eta)m), and X_{j+1}>=sqrt(X_j).

There are a prime ell in[S^2,2S^2], an odd ell-free integer M0 with exp(S)<M0<exp(DM S), and G subset[1,X_0] such that:

* ell does not divide C, and |[1,X_0] minus G| <= epsilon(S)X_0, where epsilon(S)=o(S^-A) for every fixed A;
* for each u in G and each nu=0,1, u/(ell^nu M0 C) has an expansion into at most B log S distinct odd unit fractions, all of whose denominators have ell-adic valuation exactly nu;
* B and all thresholds are absolute.

The common G, its sparse exceptional set, and the two distinct valuation classes are essential parts of this statement.

## 2. Marker and denominator supply

By the PNT, [S^2,2S^2] contains >>S^2/log S primes. At most log C/(2log S)=O(S/log S) of them divide C. Choose ell not dividing C. For large S, ell>11 and ell<S^K.

Take the source deterministic list T0 of the 2^m subset products of distinct primes in[S^K,2S^K], and its R random lists Ti, whose entries are products of m independent choices from 2m labelled prime samples. Each Ti retains its indices. Let a=ceil(D0 log S/log5) and replace the source's binary factor by

    M0 = 7*5^a * product(all deterministic and all sampled prime factors).

This is odd and ell-free. All list entries divide M0. The source size proof still gives exp(S)<M0<exp(DM S), even with the extra polynomial factor ell: the leading coefficient (2R+1)K is strictly below DM. Every deterministic t>=1; every random t>=S^(Km)>exp(S) for large S. Every t<=exp((K+1)S).

For the terminal range u<=S^D0 use the base5 expansion u=sum_j b_j5^j, 0<=b_j<=4, j<=a. The following explicit distinct odd templates have all denominators prime to5, and all their prime factors at most11:

    1/7 = 1/7;
    2/7 = 1/7 + 1/9 + 1/33 + 1/693;
    3/7 = 1/3 + 1/11 + 1/231;
    4/7 = 1/3 + 1/7 + 1/11 + 1/231.

For each nonzero digit, multiply its template denominators by ell^nu M0/(7*5^j). This represents b_j5^j/(ell^nu M0). The multiplier is a positive odd integer. Denominators at different j have different 5-adic valuations, because the templates are 5-free. Thus the combined list is distinct, has at most4(a+1)=O(log S) terms, and every denominator has ell-adic valuation nu. This replaces the binary stage without any duplicate-removal theorem.

## 3. A residue step with constrained multiplier

For Q=C_j, seek a positive integer z congruent to1 modulo2ell with

    h=uz-Qt,  0<=h<delta*u.

This occurs precisely when {Qt/(2ell u)} belongs to the interval ((1-delta)/(2ell),1/(2ell)] (with the integer part determining z). Its length is delta/(2ell). The source Erdős–Turán inequality applies to this interval; endpoint conventions are handled exactly as in its discrepancy lemma. With w tending to infinity, take

    delta=exp(-eta w), H=ceil(2ell exp(4eta w)),
    Fourier threshold = exp(-3eta w)/(2ell).

If all Fourier moduli through H are at most that threshold, the discrepancy is o(delta/(2ell)), uniformly for ell<=2S^2 and w>=D0 log S or w comparable to m. Indeed the 1/H term and the harmonic frequency sum are bounded by O(exp(-4eta w)/ell + (log H)exp(-3eta w)/ell). At least delta |T|/(4ell) indexed entries then succeed.

For each successful entry the exact identity is

    u/(ell^nu M0 Q)
      = 1/((ell^nu M0/t)z) + (1/z) h/(ell^nu M0 Q).

The multiplier z is odd and ell-free. In every use Qt>u: at high levels Q=C> X_0, while at the other levels the random t>exp(S)>=u. Hence h<Qt. The residual sum is strictly smaller than the first unit fraction, since their ratio is h/(Qt). Any positive expansion of the residual therefore has all denominators strictly larger than the first one. This is the internal distinctness invariant.

## 4. Exact Fourier estimates and simultaneous selection

### High levels

For fixed frequency l<=H with w=m, expand the square over the deterministic distinct list. The diagonal is at most2^-m. Off diagonal the phase is Z/u with

    Z=l C(t-t')/(2ell).

Our stronger C range gives |Z|>=exp(DC S) for large S. Also |Z|<=exp((2DC+K+2)S). On each dyadic interval of u in(X_{j+1},X_j], the source bounds exp(.8S)<=U<=exp(DX S) give U^4<=|Z|<=U^(3DC). Thus the actual reciprocal-phase lemma applies unchanged, including to the nonintegral real Z. Its normalized second moment is at most2^-m+O(exp(-cS))<=exp(-.01m), as in the source proof. Markov and the union over H frequencies give at most

    O(ell^3) exp((10eta-.01)m) X_j <= X_j exp(-.008m)

bad integers at a high level.

### Extended random estimate

The source random-product lemma is needed at modulus v=2ell u, not u. Its stated upper range log v<=S must be extended to log v<=2S. Here is the full range check in its proof. For D0 log S<=V=log v<=2S set s=floor(.75 V/(K log S)). Then .74 V/(K log S)<=s<=.75 V/(K log S), and 2s<=.031m<m/4 for large S. The Hamming-distance exception is still at most exp(-m/16). Expose all except two disjoint groups of s fresh I-selected factors, as in the source proof, and write t_I=U0 U1 U2. For l<=exp(.005 min(m,V)), put q=v/gcd(lU0,v). If q<v^.9 then gcd(U0,v)>v^.095. This needs at least k0=ceil(.08V/((K+1)log S)) sampled prime hits on v. There are at most2S eligible primes dividing v, so the union bound over at most m<=S independent positions is at most

    (2S^2/P)^k0 <= S^(-(K-4)k0) <= v^(-.05),

where P>=S^(K-1). All constants have slack: .08(K-4)/(K+1)>.05. On the complementary event q>=v^.9, each fresh product is below v^.7575<q, and unique factorization bounds each atom by s!/P^s<=v^(-.7252)<=v^(-.7). Orthogonality on Z/qZ and Cauchy–Schwarz give the same bilinear bound sqrt(q)||alpha||2||beta||2<=v^(-.2). Therefore

    E |2^-m sum_I e(l t_I/v)|^2
      <= exp(-m/16)+v^(-.05)+v^(-.2)
      <= exp(-.01 min(m,V)).

This proves the extension, with absolute onset, including composite v and all gcd possibilities.

At middle levels u<=exp(S), v=2ell u<=exp(2S). For w=m in the discrepancy test, min(m,log v)>=(1-eta)m. The maximum frequency H obeys log H<=4eta m+O(log S)<.005 min(m,log v). Markov and the frequency union give failure probability <=exp(-.008m). Consequently with probability1-o(1) the number of bad u at every middle level is <=X_j exp(-.001m), by Markov again and d=O(log S).

At terminal integers S^D0<u<=exp(m), use w=log u. Now min(m,log v)>=w. Further log H<=4eta w+3log S<=.00043w<.005min(m,log v) eventually. The probability a given block fails is <=O(ell^3)u^(-.009)<=u^(-.008) for large S, because w>=100000log S. The R=1000 independent blocks fail simultaneously with probability <=u^-8. Summing over all terminal u is o(1). Thus one realization supplies all middle-level bounds and a successful constrained step for every terminal u. The high levels are deterministic. At every nonterminal level the successful degree is at least rho |T|/(4ell), outside at most X_j exp(-.001m) exceptions.

## 5. Descent and exception recurrence

Start with the explicit digit templates below S^D0. For S^D0<u<=X_d<=exp(m), a successful terminal step gives h<u^(1-eta). Iterating reaches the digit range in O(log S) steps. All steps preserve oddness and ell-adic valuation, and the strict residual inequality from section3 gives distinctness at every step.

Work backwards through the source levels. Define G_d=[1,X_d]. For j<d, include inherited members of G_{j+1}, and include u<=X_j if some successful list entry has h in G_{j+1} or h=0. Use the same definition for nu=0 and1; it contains no M0 or nu. When C changes to1, rescale the child expansion by C. This is odd and ell-free. The exact identity becomes

    u/(ell^nu M0 C_j)
      =1/((ell^nu M0/t)z)
       + 1/(z C_j/C_{j+1}) * h/(ell^nu M0 C_{j+1}).

Inherited expansions are rescaled by C_j/C_{j+1}. Thus all constructed expansions have the required distinctness and valuation and use O(log S)+d terms.

Let delta_j=|[1,X_j] minus G_j|/X_j. For a fixed bad residual h and list index t, every predecessor u divides C_jt+h. The additional congruence on z only reduces the predecessors. With N=C_jt, the source divisor-moment lemma applies: log X_j is between S/(2log S) and DX S; X_{j+1}>=sqrt(X_j); and N<=exp((2DC+DM+2)S). For fixed r>=max(2,8Kd), alpha=1-1/r, Hölder and the successful-degree bound give

    delta_j <= exp(-.001m) + rho delta_{j+1}
                +4ell exp(S^(1/4)/r) delta_{j+1}^alpha
             <= epsilon0 + exp(2S^(1/4)) delta_{j+1}^alpha.

The last inequality holds uniformly since ell<=2S^2. Starting at delta_d=0 and using alpha^d>=S^-1/4 yields

    delta_0 <= d exp(2r S^(1/4)-.001m S^-1/4).

This is o(S^-A) for every fixed A. All constants, including r, were fixed before S tends to infinity. Set G=G_0 and epsilon(S) to this last bound. This proves section1's entire assertion.
