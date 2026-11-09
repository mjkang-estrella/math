# H026 — Counting inputs with any base-smooth low-energy residual

2026-10-08. **Unreviewed parent proof.**
Dependencies: accepted H021 coefficients, H024 feasible cutoff and diagonal
count, and H025's fixed-universe viewpoint. No experiment or Lean theorem.
Verified full factoring complexity improvement: **NONE**.

## 1. The exact supply question and fixed universe

Let ell=bit_length(N)>=2, k=ell, p_1,...,p_ell the first ell primes,
f_j=ceil(j/2), and use the exact bounded-error logarithm coefficients of
H021 and the feasible cutoff E_star(N) of H024. It is accepted that

    0<E_star(N)<40ell².

Let S_N={e:F_N(e)<=E_star(N)}. This set is nonempty because it contains
the feasible vector used to define the cutoff. Every S_N lies in the
N-independent finite set

    U_ell={e in Z^ell:q(e)=sum f_j²e_j²<=40ell²},
    |U_ell|<=exp(K ell^(2/3)), K=11*40^(1/3).          (1)

For e in this universe define fixed positive integers

    u_e=product p_j^max(e_j,0),
    v_e=product p_j^max(-e_j,0),
    w_N(e)=u_e-Nv_e.

A nonzero residual is called base-smooth precisely when every prime divisor
of |w_N(e)| is among p_1,...,p_ell. Magnitude one is included.
Zero is treated separately and does not count as a smooth parity relation.
The proposed theorem is about this particular base, not every polynomial
factor base allowed by H021.

## 2. Explicit width for the whole diagonal universe

The accepted prime-generation bound gives p_j<=4(j+1)² for every j>=1.
Consequently log p_j<=4 log(j+1), and f_j>=j/2 gives

    sum_{j>=1}(log p_j/f_j)²
       <=64 sum_{j>=1} log²(j+1)/j² <768.             (2)

For an explicit justification, divide the latter sum into
2^r<=j<2^(r+1), r>=0. Each block contributes at most
(r+1)²(log2)²/2^r. The sum of (r+1)²/2^r is 12 and log2<1, proving (2).

Cauchy–Schwarz, q(e)<=40ell² and 176²>40*768 imply

    sum_j |e_j| log p_j <176ell.
    
Thus log u_e,log v_e<176ell. For ell-bit N, log N<ell log2<ell, so

    0<=|w_N(e)|<=max(u_e,Nv_e)<exp(177ell)=X_ell.       (3)

This holds for all of U_ell, not merely its N-dependent accepted subset.
The constants are deliberately loose; no practical threshold is claimed.

## 3. A subexponential upper count of smooth residual values

Let Psi_ell(X) count positive integers at most X whose prime divisors are
among the first ell primes. For any real sigma>0, unique prime factorization
and finite products of convergent nonnegative geometric series give

    Psi_ell(X)
       <= X^sigma product_{j<=ell}(1-p_j^(-sigma))^(-1).  (4)

Indeed 1<= (X/n)^sigma for n<=X, and the sum of n^(-sigma) over all
integers supported on this finite prime set factors into that product.
This is an inequality, not an assertion of probabilistic independence.

For sufficiently large ell, put

    sigma=2 log log ell / log ell,    0<sigma<=1.

Since p_j>=j+1, split the product at j=floor(sqrt(ell)).
For its at-most-sqrt(ell) small-index terms, p_j>=2 and

    1-2^(-sigma)>=sigma log2/2,

using 1-exp(-y)>=y/2 for 0<=y<=1. Their total logarithm is at most

    sqrt(ell) * log(2/(sigma log2)).                   (5)

For every remaining j, p_j>sqrt(ell), hence
p_j^(-sigma)<=1/log ell<=1/2 eventually. The inequality
-log(1-z)<=2z for 0<=z<=1/2 bounds their total by 2ell/log ell.
Using X=X_ell from (3) in (4) proves

    log Psi_ell(X_ell)
      <= 354ell log log ell/log ell
           +2ell/log ell
           +sqrt(ell) log(2/(sigma log2))
       = O(ell log log ell/log ell)=o(ell).            (6)

No prime-density estimate is used in (4)–(6); the elementary bound
p_j>=j+1 suffices. The first-prime upper bound in section 2 controls widths.
There is no Dickman heuristic, random-residue model or unproved smoothness
distribution in this calculation. Small ell may be omitted from this
asymptotic claim, or handled by the finite product (4).

## 4. A deterministic count of inputs with any smooth residual

For each fixed e and each signed integer w, the identity

    N=(u_e-w)/v_e                                    (7)

determines at most one integer N. It may determine none in the ell-bit
interval. There are at most 2Psi_ell(X_ell)+1 eligible signed values if both
nonzero base-smooth residuals and zero are counted. It follows that the
number A_ell of ell-bit inputs admitting any such residual from U_ell is

    A_ell <= |U_ell| [2Psi_ell(X_ell)+1]
          <= exp(O(ell^(2/3)+ell log log ell/log ell))
           = exp(o(ell)).                            (8)

Overlaps and repeated representations only reduce the input count. This
does not presume an injective map from pairs to N or a uniform residue
distribution. Enlarging from S_N to U_ell is safe. Arbitrary selection,
optimization and randomization after seeing N cannot create a qualifying
vector outside the union.

Under the uniform distribution on all ell-bit inputs the qualifying
probability is therefore at most

    exp(-(log2)ell+o(ell)).                           (9)

This is an upper bound on that probability, not its exact asymptotic value.
For a nonqualifying N the entire exact accepted set S_N has zero nonzero
base-smooth residuals, even though S_N itself is nonempty.

This already proves an unconditional input-density statement. To refute
an all-large-composites supply lemma after small-prime removal, the remaining
section supplies an explicit exponentially large composite comparison set.

## 5. Balanced squarefree semiprimes and the missing all-input lemma

Let x=2^((ell-1)/2). Choose distinct primes p<q in the open interval
(x,sqrt(2)x). Their product satisfies

    2^(ell-1)<pq<2^ell,    1<q/p<sqrt(2).

These are ell-bit squarefree balanced semiprimes. For large ell, both primes
exceed p_ell since p_ell<=4(ell+1)² whereas x grows exponentially. All are
therefore coprime to the generator's prime base.

For the required prime count, I checked Rosser–Schoenfeld's primary paper,
page 69, Corollary 1 equations (3.5)–(3.6):

    pi(y)>y/log y for y>=17,
    pi(y)<1.25506 y/log y for y>1.

[Primary prime-count bounds](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).
These are the only new external quantitative premises here; the following
interval/product comparison is derived from them.

The number R_ell of primes in the open interval is at least

    pi(sqrt(2)x)-pi(x)-1
      > x/log x *[sqrt(2) log x/log(sqrt(2)x)-1.25506]-1.

The bracket tends to sqrt(2)-1.25506>0, so
R_ell=Omega(x/log x). Unique factorization makes every unordered pair of
distinct primes a distinct semiprime. Consequently the set B_ell of the
displayed products has

    |B_ell|=binom(R_ell,2)=Omega(2^ell/ell²).          (10)

This statement uses no claim about semiprimes in the special H023 family.
It is an explicit conventional interval-product ensemble.

By (8) and (10), the fraction of B_ell admitting any nonzero base-smooth
residual in S_N is at most exp(-(log2)ell+o(ell)), hence tends to zero.
In particular, for every sufficiently large ell there are members of B_ell
with *no* such residual. More strongly, their proportion tends to one.

Thus the precise supply question in H024's review has a negative answer
for this cutoff and base: there is no fixed A>0 for which every sufficiently
large composite N coprime to the base has at least an ell^(-A) fraction of
S_N producing nonzero p_ell-smooth residuals. For the constructed existence
argument most inputs have fraction exactly zero. This is an existence and
density argument, not a polynomial-time algorithm enumerating the failing
semiprimes without their factors or identifying a numerical threshold.

## 6. Exact scope and next action

If accepted, this closes the proposed inverse-polynomial smooth-supply lemma
for the specific fixed first-ell-prime universe at the cheap H024 energy
cutoff. It removes the hypothetical randomness law used only conditionally
in H024. It does not show that factoring is hard, or exclude another branch
of a factoring algorithm.

There is no claim of novelty for the elementary Euler-product/encoding count.
There is no statement about the paper's post-LLL correction domain or
perturbed tensor-network sampler. Larger energy changes both vector count
and output widths. A larger factor base changes Psi and may invalidate its
o(ell) logarithmic bound. An N-dependent base or different weights changes the
common universe. A polynomial number or exp(o(ell)) family of universally
controlled versions could be union-bounded, but no unrestricted adaptive
family is covered or constructed here.

Finite constants are loose, and the asymptotic upper bound may be vacuous
at practical bit lengths. Neither toy experiments nor fast DP timing would
establish the theorem. No computation, benchmark or shared infrastructure
change is needed to review these claims.

Next action: independent review of every inequality, the probability-free
pair count, the semiprime denominator and exact rejection scope. If it passes,
record this branch's supply obstruction and pursue a materially changed,
costed mechanism rather than implementing the same low-energy generator
as a general factoring candidate.
