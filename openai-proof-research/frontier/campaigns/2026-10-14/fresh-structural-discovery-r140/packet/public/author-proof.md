# T205Q140 — Sharp two-step Plancherel approximation for staircase tensor walks

Research author proof, at the unchanged scope in frozen-scope.md. Codex / GPT-6 Astra / high / default service tier. Original prose CC BY 4.0; original code MIT. No independent gate is assigned. This is not a manuscript or release-stage artifact.

All measures below are on ALL partitions of n=m(m+1)/2, m>=2. Write r_lambda(C)=chi_lambda(C)/d_lambda. We prove every frozen assertion. The proposed residual contribution is the all-support sum in Section 4. The spectral transform, character bounds, core vanishing and Gaussian limit are credited inputs.

## 1. Paid operations and precise dependencies

[F] Fulman, *Stein's method and random character ratios*, retained author-hosted revised PDF, Sections 3.1–3.3, especially Lemmas 3.2–3.7, Corollary 3.8 and Theorem 3.14. These supply character orthogonality, the tensor kernel and its eigenbasis, and the unit-variance character CLT for any fixed cycle length. We use i=3.

[FM] Fulman, *Convergence rates of random walk on irreducible representations of finite groups*, final author revisions April13,2007, Lemma2.1 and Section3, gives the exact spectral/chi-square identity and tensor-power distribution. Its symmetric-group application tensors with the defining representation, a different kernel.

[FS] Féray–Śniady, *Asymptotics of characters of symmetric groups related to Stanley character formula*, arXiv:math/0701051v4, Theorem1, proved in Section5.1 using Section4. For an absolute A>=1, every diagram lambda of n boxes and permutation sigma satisfy

    |r_lambda(sigma)| <= [A max(rows(lambda)/n,
                              columns(lambda)/n, |sigma|/n)]^|sigma|. (1)

Here |sigma| is transposition length, not support size. The factorization and coloring estimates proving (1) are paid.

[T] Teyssier, *Bounds on skew dimensions and characters of symmetric groups via thick hook decompositions*, arXiv:2508.06770v2, September16,2026, Theorem1.2. For each fixed balance constant B0, uniformly over diagrams with maximal hook <=B0 sqrt(n), there is B>=1 such that for sufficiently large n and all nonidentity sigma,

    |r_lambda(sigma)| <= [B/sqrt(|sigma|)]^|sigma|.                   (2)

Its proof uses thick-hook/Naruse estimates, restriction to the support, and Murnaghan–Nakayama counts (Sections2.1–2.8 and3.1–3.3). For our staircase, maximal hook=2m-1<2sqrt(2n), so B0=3 works. This is an external primary dependency, not part of the stipulated OpenAI pin. No effective numerical threshold is asserted.

Pinned source205 proves cyclic full support using its actual band quotients, dominance calculation, matrix path contractions and strip induction. The companion treats ordinary support at other degrees. These are credited and not truth-audited. The proof below does not need source205 positivity: it is a quantitative distributional statement independent of whether every finite constituent is positive. No full-support, minimum-multiplicity, signed, integral or modular assertion is inferred from total variation.

## 2. Exact cancellations and the leading class

For a partition with L rows, its beta numbers are b_i=lambda_i+L-i. A removable ribbon of length h corresponds to moving a bead b to an unoccupied nonnegative b-h; its height is the number of intervening beads. This is the usual boundary-path form of Murnaghan–Nakayama: exchanging an occupied and empty boundary step removes the intervening ribbon, with length their index difference. The source companion's finite.tex beta-set proof uses this operation.

For rho, L=m and the bead positions are 1,3,...,2m-1. If h>0 is even, b-h is negative or an already occupied odd position. No even-length ribbon can be removed. Murnaghan–Nakayama allows cycle removal in any order ([T], Section3.1.3). Removing an even cycle first therefore gives

    r_rho(C)=0 whenever C has an even cycle.                        (3)

Let T2 be the sum of all transpositions in the group algebra, T3 the sum of all3-cycles, and T22 the sum of all products of two disjoint transpositions (zero if n<4). Counting ordered pairs gives

    T2² = binom(n,2)e + 3T3 + 2T22.                                (4)

Equal transpositions give the first term. Distinct ones sharing a letter give a3-cycle with three ordered factorizations. Disjoint ones give two ordered factorizations. These exhaust the cases. A central class sum acts on an irreducible by |C|r_lambda(C), by Schur's lemma and trace. On rho, T2 and T22 have scalar zero by (3). Thus for every m>=2,

    r_rho(C3)=-binom(n,2)/(3|C3|)=-1/[2(n-2)].                     (5)

This includes n=3 without assuming a nonexistent double-transposition class.

## 3. Spectral reduction

Character orthogonality gives the orthonormal L²(pi_n) basis

    X_C(lambda)=sqrt(|C|)r_lambda(C).

The identity class gives the constant1. By [F, Corollary3.8], K_m has eigenvalue r_rho(C) on X_C. Equivalently, evaluate the character of S^lambda tensor S^rho at C and sum its irreducible decomposition. All characters here are real.

At the trivial state, X_C((n))=sqrt(|C|). The spectral formula [FM, Lemma2.1] gives

    mu_m(lambda)/pi_n(lambda)-1
      =sum_(C!=identity) sqrt(|C|)r_rho(C)² X_C(lambda).             (6)

All sums are finite. With a_n and X_n as frozen, orthogonality and (5) give

    mu_m/pi_n-1=a_n X_n+R_n,
    E_pi R_n=E_pi(R_n X_n)=0,
    E_pi R_n²=sum_(C!=identity,C3)|C|r_rho(C)^4,                   (7)
    chi²(mu_m,pi_n)=a_n²+E_pi R_n²,
    a_n²=n(n-1)/[48(n-2)³].                                      (8)

After the strongest classical reduction the debt is a nonnegative sum over ALL remaining classes. A fixed-support character asymptotic does not settle it.

## 4. Uniform fourth-moment tail over every odd-cycle profile

Let k be support size, l the number of nontrivial cycles, and t=|sigma|. By (3), only odd nontrivial cycles of length>=3 matter, so

    1<=l<=k/3,           t=k-l>=2k/3.                             (9)

For a profile (a_3,a_5,...) with sum_j ja_j=k and sum_j a_j=l, its class size is

    (n)_k/product_j(j^a_j a_j!).

Ordering the l cycles gives the exact coefficient identity

    sum_profiles 1/product_j(j^a_j a_j!)
      =(1/l!)sum_(j_1+...+j_l=k; j_i odd>=3)1/(j_1...j_l).

There are at most2^(k-1) ordered compositions of k and every reciprocal product is<=1. The total size of these classes is therefore at most

    2^k n^k/l!.                                                   (10)

Also, for1<=l<=k,

    1/l!<=e^k k^(-l).                                             (11)

Indeed l!>=(l/e)^l; with x=l/k, (ek/l)^l=exp(kx(1-log x))<=exp(k).

All constants D below are fixed independently of m,k,l and may increase to absorb fixed exponential factors. Summing over at most k values of l can be absorbed using k<=2^k.

**Small support: k<=sqrt(n).** We have m/n<=sqrt(2/n), t/n<=n^(-1/2). Equation(1) bounds the fourth power by D^k n^(-2t). With(10), the contribution at k,l is at most

    D^k n^(-k+2l)/l!.                                             (12)

There are no allowed profiles at support1,2 or4. At support3 there is just C3, already separated. At support5, l=1 and(12) is O(n^(-3)). At every k>=6, -k+2l<=-k/3. Summing l and then k from6 to sqrt(n) is at most

    sum_(k>=6)(D n^(-1/3))^k=O(n^(-2)).                           (13)

Empty ranges contribute zero.

**Intermediate support: sqrt(n)<k<=n^(2/3).** Now m/n<=sqrt(2)k/n. Equation(1) bounds the fourth power by D^k(k/n)^(4(k-l)). With(10) and(11), the contribution at k,l is at most

    D^k n^(-3k+4l) k^(4k-5l).                                    (14)

Its l-dependent factor (n^4/k^5)^l increases in l in this range. Hence l<=k/3 gives

    n^(-3k+4l)k^(4k-5l)
      <=n^(-5k/3)k^(7k/3)
      <=n^(-k/9).                                                 (15)

Discarding the factorial in(10) would lose this summable exponent. No bounded-cycle-length assumption has been made.

**Large support: k>=n^(2/3).** Since t>=2k/3, equation(2) bounds the fourth power by D^k k^(-2(k-l)). With(10) and(11) the contribution is at most

    D^k n^k k^(-2k+l)
      <=D^k n^k k^(-5k/3)
      <=(D n^(-1/9))^k.                                          (16)

This includes linear support up to k=n. Any overlap at the integer boundary can be assigned to either range, or counted twice in an upper bound.

After summing l, both large ranges together are bounded by

    sum_(k>sqrt(n))(D n^(-1/9))^k=O(n^(-2)).                       (17)

For example once D<=n^(1/18), the terms are at most n^(-k/18); the geometric tail is smaller than n^(-2) for all sufficiently large n. Equations(13) and(17) prove

    sum_(C!=identity,C3)|C|r_rho(C)^4<=C0/n²                       (18)

for all sufficiently large triangular n. The remaining set of m>=2 is finite and each sum is finite. Enlarging C0 by the maximum of their n²-weighted sums proves(18) for EVERY m>=2. This is the existential absolute constant required by the scope, not a claim to an explicit numerical constant in[T]. Equations(7)–(8) prove assertion1.

## 5. Exact worst starts and the sharp constant

For any irreducible eta, define K_eta by tensoring with eta. It is stochastic by tensor decomposition. It preserves pi_n by the reversibility identity

    pi_n(lambda)K_eta(lambda,nu)
      =d_lambda d_nu g(lambda,eta,nu)/(n!d_eta).

Associativity and commutativity of tensor products give K_eta K_rho=K_rho K_eta: both decompose the same triple tensor product with identical dimension normalization. Also delta_(n)K_eta=delta_eta. Thus for every integer s>=0,

    delta_eta K_rho^s=(delta_(n)K_rho^s)K_eta.                     (19)

Stochastic kernels contract total variation, and pi_n K_eta=pi_n. Therefore the trivial state maximizes total variation at every integer time, including1 and2. For chi-square, the spectral formula bounds each summand at eta by the trivial-start summand, since

    X_C(eta)²=|C||r_eta(C)|²<=|C|.

The last inequality follows by making the representation unitary, when absolute trace is at most dimension. This proves both exact maxima in assertion2.

Under pi_n, X_n has mean0 and variance1. By[F, Theorem3.14] with i=3, X_n converges in distribution to a standard real Gaussian Z, also along triangular n. The second moments imply uniform integrability of absolute values, since E[|X_n|;|X_n|>M]<=1/M. Hence

    E_pi|X_n| -> E|Z|=sqrt(2/pi).

By(7), (18), the triangle inequality and Cauchy–Schwarz,

    |TV(mu_m,pi_n)-(a_n/2)E_pi|X_n||
      <=(1/2)E_pi|R_n|<=sqrt(C)/(2n).                              (20)

Because sqrt(n)a_n->1/(4sqrt(3)), this yields

    sqrt(n)TV(mu_m,pi_n)->1/[4sqrt(6 pi)].                         (21)

Equations(8) and(18) yield n chi²(mu_m,pi_n)->1/48. The exact maxima then prove all of assertion2.

At time1 the trivial-start law is delta_rho, so its distance is1-pi_n(rho). Equation(19) makes it the worst-start distance. Finally(5) gives

    X_n(rho)²=n(n-1)/[12(n-2)].

The contribution of this atom to E_pi X_n²=1 implies

    pi_n(rho)<=12(n-2)/[n(n-1)]->0.                               (22)

Thus the one-step maximum tends to1, proving assertion3. We do not call this conventional cutoff, whose usual definition includes diverging mixing times. Every frozen assertion is proved in this author argument.

## 6. Strongest-reduction comparison and independent gates

Source205 support, R037's floor and R026's integral cube do not control(7). Conversely(21) does not imply their pointwise or integral conclusions. The I19/I21 physical-flip target remains unchanged.

The eigenbasis, CLT, maximum-character estimates and Teyssier's large-support theorem are not new operations. The proposed increment is(18): the uniform fourth-moment remainder after the compatible small- and large-support bounds, using odd-cycle profiles and their factorial count through the intermediate window. Whether this summation and its sharp distributional consequence are substantial or a technical composition is reserved to independent contribution review. No worldwide-priority claim is made.

No further internal mathematical debt is identified at this frozen scope. Independent adversarial proof review, separate contribution review and all later parent gates remain outstanding. The finite program checks only m=2..6 character rows and m=2..5 complete distributions; it does not prove the all-order bound or CLT. No previous switch, signed-support, thin-tree or other frozen target is resolved or narrowed.
