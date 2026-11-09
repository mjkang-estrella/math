# H024 — A feasible cutoff and an upper bound on low-energy population

2026-10-08. **Unreviewed parent derivation.**
Uses the accepted H021 construction, not the transformed LLL correction domain.
No implementation, finite experiment or Lean theorem.
Verified full factoring complexity improvement: **NONE**.

## 1. Exact feasible cutoff

Use the fixed N-only rule in H021 section 5: N>1, ell=bit_length(N)>=2,
k=ell, C the least power of ten >=ell, f_j=ceil(j/2), and its rational
round_star coefficients with |a_j-C log p_j|<=1, |T-C log N|<=1.
Here ell<=C<10ell and C>=10. In particular a_1>=C log2-1>0.

Define by integer arithmetic

    r=floor((2T+a_1)/(2a_1)),
    e_star=(r,0,...,0),
    E_star=F(e_star)=r²+(a_1 r-T)².                    (1)

Nearest-integer rounding gives |a_1 r-T|<=a_1/2 and
|r|<=|T|/a_1+1/2. Since log N<ell log2, a_1>=C log2-1,
T=O(C ell), and a_1=Theta(C), we have r=O(ell) and

    E_star<= (|T|/a_1+1/2)²+a_1²/4=O(ell²).          (2)

Both r and E_star are computed exactly; no true-log tie is being decided.
H021's rational log construction remains unchanged. Computing (1) from
its already supplied integer coefficients uses polylog(ell) bit work.

Every global minimizer has F(e)<=E_star because e_star is feasible.
The diagonal energy therefore bounds |e_j|<=floor(sqrt(E_star)/f_j),
so this finite box contains every global minimizer. This also proves
existence by minimizing over the box. No minimum-energy computation or
factor information is needed to obtain E_star. If E_star=0, positivity of
f_j makes the diagonal minimizer unique, and the usual zero-cutoff treatment
applies. The actual N-only rule has T>0, so E_star>0.

The previous E=T² cutoff was correct but loose. Reducing it can discard
higher-energy useful relations, and this report does not assert that a
global optimizer or its entire new low-energy set has useful relations.

## 2. Costs in the accepted H021 model

Write R_j=floor(sqrt(E_star)/f_j), L=sum(2R_j+1),
S=sum|a_j|R_j, Q=2S+1. Harmonic summation gives

    sum_j 1/f_j=O(log(ell+2)),
    sum_j R_j=O(ell log(ell+2)),
    L=O(ell log(ell+2)).

The accepted prime bound p_k=O(k log(k+2)) and C=O(ell) give
max |a_j|=O(ell log(ell+2)), hence

    S=O(ell² log²(ell+2)),    Q=O(ell² log²(ell+2)),
    b=O(log(ell+2)).                                    (3)

Here b is H021's complete integer width for the DP; reading N itself is
part of the separate setup and is not a b-bit operation. Thus its prefix/
suffix table bound is

    T_DP=O(ell³ log^4(ell+2))                            (4)

in the explicitly charged indexed-memory model. Rolling value memory is
O(ell² log³(ell+2)) bits; all prefix predecessors or suffix rows use
O(ell³ log³(ell+2)) bits. Worst-case enumeration delay is
O(ell log²(ell+2)) bit work plus materializing the integer output.
A prefix or a filtered domain inherits no useful-relation yield guarantee.

H021's original trial-division prime construction costs
O(ell^4 log²(ell+2)), which still dominates (4).
There is a standard explicit replacement: initialize a bit array through
U=4(k+1)²; process i=2,...,U in order; if unmarked, declare i prime and
mark its multiples 2i,3i,...<=U. Composite i was already marked by a
smaller prime, while a prime has no smaller divisor. The first k primes
therefore match H021's list. Initialization and all marking loops cost
O(U log²(U+2)) charged bit work: bound loop counts by
sum_{i=2}^U floor(U/i)=O(U log(U+2)) and charge O(log U) for indices/
indexed bit access. Memory is O(U) bits plus addresses and the output list.
No sophisticated sieve theorem or prime-distribution heuristic is used.

With this replacement, rational logs are charged exactly as in H021:
n=O(log ell), d_x=O(ell log² ell) even using the largest input width
for all k+1 logs, so total cost is O(ell³ log^5(ell+2)).
Consequently the entire N-only optimizer has a tilde-O(ell³) bound
in that indexed-memory model. This is not a proved cubic ordinary Turing
bit-complexity bound. The conservative table-scan realization in H021
multiplies table costs by O(1+kQ+L), retaining a polynomial, tilde-O(ell^6)
DP bound. An equally explicit conservative sequential realization of
prime-array accesses stays within that scale; rational arithmetic is paid
by its bit operations. No formal refinement or implementation is supplied.

For counting/unranking, retain H021's extra E coordinate and its count-bit
factor. No counting-time improvement is assumed in the supply argument below.
Constructing u,v,w also retains H021's paid output bounds. For an actually
accepted vector, Cauchy–Schwarz gives the sharper analytic size

    sum |e_j| log p_j
        <=sqrt(E_star)*sqrt(sum (log p_j/f_j)²)=O(ell), (5)

because p_j=O(j log(j+2)) and sum log²(j+2)/j² converges.
Thus each accepted u,v,Nv,w has O(ell) bits. This is an upper bound;
it does not show |w| is exponentially large, or exclude w=0.
Constructing exponents/powers is still charged, not a unit-cost operation.

## 3. Uniform upper population bound

Let q(e)=sum f_j² e_j² and
M_k(E)=#{e in Z^k:q(e)<=E}. The accepted F-set is a subset of this set.
For E=0, M_k(E)=1. For E>=1 we propose the uniform bound

    M_k(E)<=exp(11 E^(1/3)), for every finite k.         (6)

Here and below exp and log are natural. No claim of sharp constants is made.
The number of full F-vectors may be far smaller or zero for a general
supplied cutoff; (6) is only a diagonal upper bound.

For s>0 let theta(t)=sum_{n in Z}exp(-t n²). Nonnegative summation gives

    M_k(E)<=exp(sE) product_{j<=k} theta(s f_j²)
           <=exp(sE) product_{m>=1} theta(s m²)^2.       (7)

The last product reflects that each weight m occurs at most twice.
Put h(x)=log theta(x²). This is positive and decreasing. The integral
comparison, justified first for finite sums, gives

    sum_{m>=1} h(m sqrt(s))
        <=s^(-1/2) integral_0^infinity h(x) dx.         (8)

For 0<x<=1, monotonicity of the Gaussian summands gives
theta(x²)<=1+sqrt(pi)/x<=1+2/x<=3/x, hence

    integral_0^1 h(x) dx<=log3+1<3.

For x>=1, n²>=1+3(n-1) for n>=1, so

    theta(x²)-1
      <=2 exp(-x²)/(1-exp(-3x²))
      <=3 exp(-x²).

Using log(1+y)<=y and x²>=x gives

    integral_1^infinity h(x) dx<=3/e<3/2.

Thus the integral is less than 9/2, the logarithm of the infinite
product in (7) is at most 9/sqrt(s), and in particular at most 10/sqrt(s).
This finite integral also justifies passage to the infinite product and
shows its convergence; no hidden infinite computation is performed.

Choose s=E^(-2/3). Then sE+10/sqrt(s)=11 E^(1/3), proving (6).
Combining (2) and (6),

    #{e:F(e)<=E_star} <= exp(O(ell^(2/3))).             (9)

This does not prove a matching F-population lower bound, uniformity over
relations, useful density, rank, or a factoring obstruction. It also does
not bound a different cutoff, different weight sequence or post-LLL domain.
A permutation of these diagonal weights preserves the ellipsoid count,
but the particular cheap cutoff and cost derivation above used f_1=1.

## 4. What a supply conclusion would actually require

The count alone proves no useful-supply bound. It gives one precise
conditional falsifier: if a separately justified probability model for
the actual attempted low-energy vectors supplies a uniform conditional
upper bound exp(-kappa ell), for some fixed kappa>0, on a new useful event
at each distinct paid attempt, then even examining all vectors gives

    E[number of new useful events]
       <=exp(O(ell^(2/3))-kappa ell) ->0.              (10)

Markov's inequality then bounds probability of any such event by the same
quantity. No independence is needed, but the per-attempt conditional bound
must hold under the selection and stopping history, not just for an
unconditional uniform sample. Alternatively a directly proved aggregate
bound suffices. This is a conditional model statement, not a fact about
the actual deterministic residuals u-Nv.

A heuristic about random integers of exponential size being smooth over
a polynomial base would not establish that law for this structured set.
Equation (5) is an upper size bound, not a lower size bound. Unusually small
w, zero residuals, favorable N, arithmetic correlations, or a better selector
could invalidate the assumed exponential rarity. These must be analyzed
rather than dismissed. Zero residuals retain H021's separate smooth-input
interpretation; zero is not an ordinary parity relation.

Conversely, a polynomial useful-density claim would have to explain how this
specific set avoids any applicable rarity law and yields enough new useful
rows with proper splitting. Neither exact minimization nor (9) does that.
Higher energy, larger rounding scale or a changed factor base alters the
question and pays its new range/output costs.

## 5. Next decisive action

Independently review (1)–(10), especially the full setup/model accounting and
the probability quantifiers. If accepted, the next substantive candidate
needs a mechanism producing unusually small residuals or a specified
non-random useful distribution at a costed cutoff. Merely implementing the
DP and observing toy minima would not answer that missing step.

This is a standard feasible-point and theta-product argument with no novelty
claim. No primary empirical resource fit is being promoted to a proof.
The accepted source-domain distinction and bounded-error log construction
remain in [H021](H021-structured-lattice-generator.md). All new mathematics
and costs in this note require review before acceptance.
