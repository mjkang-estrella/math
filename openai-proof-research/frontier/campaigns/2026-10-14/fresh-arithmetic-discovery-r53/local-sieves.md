# Local sieves before a good preimage is known

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

This is author proof development for the unchanged T024W52. All logarithms are natural; log_j denotes iteration. Ford references are to the retained author PDF and 2023 sieve notes. These are classical primary dependencies, not discoveries. The pinned source024 is denoted S.

## 1. Working scales and classical inputs

Let Y tend to infinity, B=log_2 Y, x in [Y/4,3Y/4], and c_1 Y/log Y <= h <= c_2 Y/log Y, where c_1,c_2>0 are fixed and x+h<=Y. Constants may depend on c_1,c_2. We write J=(x,x+h]. All estimates below are uniform in x,h. Changing the fixed constants only changes implied constants.

Ford Theorem4 says that, for each admissible theta, V(t+l)-V(t) is bounded above by C_theta l V(t+l)/(t+l) whenever l>=t^theta. We use theta=0.9, admissible by the classical quantitative PNT. Thus, when t lies between a fixed positive power of Y and O(Y), and l/t is comparable to1/log Y,

    V(t+l)-V(t) <= C l W(CY)/log Y,               (1)
    W(z)=max_{2<=u<=z} V(u)log u/u.

The same holds with a bounded additive shift at either endpoint. Ford's explicit order scale Z is eventually increasing and V(u)<=C u Z(u)/log u, while Z(CY)~Z(Y) for fixed C. Hence W(CY)<=C Z(Y). The source gives Z(Y) comparable to G_m(Y). These uses need only the stated order estimates, not the theorem being proved.

Other classical inputs, all displayed in the retained primaries, are:

* Ford Lemma2.2: #{n<=z: Omega(n)>=alpha log_2 z} <<_alpha z(log z)^{1-alpha log2}log_2 z for alpha>=2.
* The smooth-number estimate in the proof of Ford Lemma2.3: Psi(z,z^{2/log_2 z}) << z exp(-(log_2 z)(log_3 z)/3), in the large-z range.
* Ford Lemma2.7: the number of totients <=Y for which the value or any preimage is divisible by d^2 for some d>D is O(Y log_2 Y/D).
* The quantitative PNT pi(z)=li(z)+O(z exp(-c sqrt(log z))).
* Ford2023 Theorems2.4 and2.5, respectively the upper sieve with sum of remainder terms, and the coefficient-uniform prime-form sieve. Translation of the integer argument changes no determinant or number of roots modulo a prime.

## 2. Local bad-normal-prime count

Use exactly Ford's definition of S-normality. Suppose

    exp(B^36) <= S <= Y,
    Y^{2/5} <= z <= C Y,
    c z/log Y <= l <= C z/log Y.

Then the number of non-S-normal primes in (z,z+l] is

    << l B^5/(log Y) * (log S)^(-1/6).            (2)

The constants are uniform in S. This is needed only for large-prime intervals; small primes will be handled globally.

Proof. Apply Ford's Lemma2.6 decomposition at the ambient endpoint Z=2(z+l), so log Z is comparable to log Y and log_2 Z=B+O(1). The interval is above sqrt Z for large Y. Remove integers p-1 with largest prime factor at most Z^{2/log_2 Z}, with Omega(p-1)>=10 log_2 Z, or divisible by q^2 for a prime q>=S. Their respective global counts are at most

    Z exp(-c B log B),
    C Z (log Z)^{1-10 log2} log_2 Z,
    C Z/S.

Each is smaller than the right side of (2), uniformly in S<=Y: that right side is at least a constant times Z (log Y)^(-13/6), apart from its harmless positive B^5 factor. The middle exponent is approximately -5.93; the other two errors are still smaller. This is a legitimate use of absolute global bounds because their errors beat the local scale explicitly.

For a remaining bad prime write p-1=q b, where q=P^+(p-1)>Z^{2/log_2 Z}. Removing q changes each relevant prime-factor count by at most one. Thus b has one of the two bad-cofactor properties in Ford's proof: excessive factors below S, or excessive deviation on one of the double-exponential mesh intervals. The reciprocal sums in that proof are unchanged:

    sum_{bad b of first kind} 1/b << log Z (log S)^(-0.3),
    sum_{bad b of second kind} 1/b << log Z B^2 (log S)^(-1/6).   (3)

The second bound includes all O(B^2) mesh pairs. Prime powers below S are included in the Euler factors; squarefreeness above S is supplied by the removal just made. The inequalities also cover S>Z, when the second kind is empty and the first-kind calculation uses b<=Z. Here log S<=C log Z, so the exceptional initial case log S>(log Z)^6 in Ford's proof never occurs.

For fixed b, the q interval has length l/b, and its upper ambient endpoint is U=Z/b. A nonempty interval has U>=q>Z^{2/log_2 Z}. Consequently

    log(l/b) >= (1/2)log U >= log Z/log_2 Z

for sufficiently large Y. Translate this interval to initial positive integers and apply the two-form sieve to q and bq+1. In the middle singular-factor bound of Ford2023 Theorem2.5, primes dividing b have one root instead of two; hence the singular loss is O(b/phi(b)), not its square. Since b/phi(b)<<B, the number of q is

    << (l/b) B/(log(l/b))^2
     << l B^3/(b (log Y)^2).                    (4)

For an inadmissible pair there are at most two inputs; (4) absorbs them because its right side tends to infinity uniformly over nonempty intervals. The same lower bound absorbs rounding the interval endpoints. Combining (3)-(4) proves (2). Every changed step has been identified: only the top two-prime count changes from the global proof, and all bad-cofactor reciprocal sums stay global upper bounds.

## 3. Local S-niceness by a hyperbola split

Let S satisfy exp(B^36)<=S<=Y. Define S-nice values exactly as Ford Definition2: Omega(v)<=5log_2 v; no square d^2 with d>S^{1/2} divides v or any preimage; and every prime in every preimage is S-normal. Then

    #{v in V intersect J: v is not S-nice}
       << h W(CY) B^6/(log Y) * (log S)^(-1/6).  (5)

This statement is established before any simplex condition or good-prefix representation is assumed.

The first condition fails for at most C Y(log Y)^{1-4.9log2}B values, by Ford2.2; on J, 5log_2 v>=4.9B for large Y. This is O(Y(log Y)^(-2.39)B), smaller than (5) since h is comparable to Y/log Y and log S<=log Y. The square condition fails for at most C YB/S^{1/2}, also smaller than (5).

For the remaining condition take ANY preimage n of v and a bad prime p dividing it. Writing n=p n', one has exactly

    v=(p-1)phi(n') if p does not divide n',
    v=p phi(n')   if p divides n'.               (6)

Overcount both possibilities; this counts the union of values with at least one bad preimage, not just values whose chosen preimage is bad.

For p<=sqrt Y, the remaining totient lies in an interval with endpoint comparable to Y/p>=sqrt Y and relative length comparable to1/log Y. Equation(1) bounds its count by

    C h W(CY)/((p-1)log Y).

The global Ford2.6 bound and partial summation give

    sum_{p<=sqrt Y, p bad}1/(p-1) << B^6(log S)^(-1/6).

This proves (5) for these primes without assuming that the remaining totient has a good preimage.

For p>sqrt Y, reverse the order of summation in (6). The remaining totient w is at most C sqrt Y. For fixed w, p lies in one of two intervals centered at x/w or1+x/w, of length h/w. These satisfy the hypotheses of (2). Thus their total is

    << h B^5/(w log Y) (log S)^(-1/6).

Finally sum over distinct totients w<=C sqrt Y. Partial summation of V(t)<=tW(CY)/log t gives sum 1/w << W(CY)B. This proves (5). Repeated primes in n are covered by the second formula in (6); no squarefree preimage hypothesis was smuggled into this argument.

## 4. Local rough-number sieve and first simplex failure

For an interval of integers of length T, with 2<=S<F<=T^{1/10}, the number having no prime divisor in (S,F] is

    << T log S/log F.                            (7)

Indeed apply Ford2023 Theorem2.4 with g(p)=1/p on (S,F] and0 otherwise. Translating the interval preserves the remainder bound |r_d|<=1. With sieve endpoint F, the remainder sum is at most F, and the main product is comparable to log S/log F by Mertens. The remainder is absorbed by T/log F. The dimension bound is uniform.

This gives the following local version of Ford4.1 in its needed range. Retain its k and thresholds E_j, with exp(B^36)<=S<=exp((log Y)^0.01), E_1>S, and S<Y^{1/(20B)}. These additional auxiliary range conditions are verified below for every active mesh; no general statement at E_1=S is being invoked. Count S-nice values in J with some preimage q_j(n)>=E_j for1<=j<=k. In the proof, put F=min(E_1,Y^{1/(20B)}) and let m be the part of v supported on (S,F]. The nice Omega condition gives Omega(v)<=5B, hence m<=F^{5B}<=Y^{1/4}. Thus h/m>=cY^{3/4}/log Y and F<=Y^{1/(20B)}<=(h/m)^{1/10} for all large Y. The condition S<F is checked below for every mesh actually used. These inequalities are established before applying (7), uniformly in the extracted m. Its count is

    << (h/m) log S/log F.

This replaces precisely Y/m by h/m in Ford4.1. The S-normality lower bounds for Omega(m,E_j,E_{j-1}), the factorial reciprocal sums and the exponential-tail estimates remain unchanged. Squarefreeness above S comes from S-niceness. Thus Ford4.1's bound has the same exponents with h replacing Y (one may retain a harmless h/(log Y)^2 remainder).

Combining this with (5), and repeating the explicit finite theta-mesh argument of Ford4.2, yields its local bound:

    #{v in V intersect J: some preimage has sum_{j=1}^k a_j x_j(n;Y)>=1+omega}
      << h W(CY) B^6/(log Y)
          * exp[-omega^2 B/(600 k^3 log k)],       (8)

for k>=2 and0<omega<1/10. To check the parameter cases: if omega^2<=3600(log B)k^3log k/B, the right side is at least a constant times hW(CY)/log Y, so (1) suffices. Otherwise choose log_2 S=omega^2 B/(100k^3log k). Then S>=exp(B^36), and S<=exp((log Y)^0.01); (5) and (7) apply. Here are the endpoint checks for the theta mesh. Set alpha=sum_{i=1}^k a_i<k log k and sigma=log_2 S/B. Ford's mesh has 0<=theta_k<=...<=theta_1<=1 and sum a_i theta_i in[1+0.9omega,1+omega]. The upper bound theta_1<=1 holds because q_1<=sqrt(n), n<<YB, so q_1<Y for large Y. Drop coordinates theta_i<sigma and let j be the last retained index. Their entire weighted contribution is at most alpha sigma<=omega^2/(100k^2)<omega/100. Hence j cannot be0 or1: if at most one remained the total weighted sum would be at most a_1+omega/100<1. Also theta_1>=(1+0.9omega)/alpha>sigma, so E_1=exp(exp(theta_1 B)) is strictly larger than S. Since sigma<0.01, S<Y^{1/(20B)} for all sufficiently large Y, uniformly in the active parameter range. Therefore F=min(E_1,Y^{1/(20B)})>S. These checks cover zero mesh coordinates and coordinates exactly at or just below sigma; the last retained coordinate may equal sigma without affecting the strict first-coordinate gap. For the retained list j>=2, the previous local Ford4.1 argument is valid, with all its sieve ranges verified. Ford's same mesh has at most(10k log k/omega)^k choices and its nice contribution is O(h(log Y)^(-1-omega/4)). The bad-nice contribution is exactly bounded by (5). The same exponent comparisons give (8).

The argument is not a subtraction of two global error estimates. It counts the first-failure values directly in J, before any normal coordinate bands are known.
