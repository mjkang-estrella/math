# Independent ordinary review of finite concentration replacement

Verdict: PASS with explicit empty-cell convention below. Reviewed solo on 2026-10-30 against frozen/03-FINITE-CONCENTRATION.md (SHA-256 01240e466f63df3b9041c386f80afc0e9290593ab0ae53df80f26c7a5107cb1d). This is an ordinary mathematical review, not Lean verification. The original reviewed Fourier argument remains intact in frozen/00-PROOF.md; no correction requiring its restoration was found.

Let m>=1, 0<a<=p_i<=1/2. On a fresh finite product space choose all 2m coordinates U_i,V_i mutually independent, with U_i Bernoulli(2p_i) and V_i Bernoulli(1/2). Define B'_i=U_i V_i. Each success probability is (2p_i)/2=p_i; disjoint coordinate pairs give independence. Thus the entire B'-vector has the original B-vector law, not merely matching marginals. At p_i=1/2, U_i=1 deterministically, which causes no exception.

For every U-vector u with positive probability, the V-vector remains a product of fair bits, and the sum of B'_i is the sum of exactly K(u) of those bits. Its law is Binomial(K(u),1/2). Conditioning on null u-vectors is unnecessary: one can sum joint masses directly over u, ignoring zero weights. Conditional on K alone the same conclusion follows by mixing identical Binomial(K,1/2) laws, but conditioning on the full U-vector is the direct justification.

Write mu=2 sum p_i>0. Independence gives Var K=sum 2p_i(1-2p_i)<=mu. The event K<mu/2 implies |K-mu|>=mu/2; Chebyshev yields probability <=4/mu. This bound may exceed one for small mu, which is harmless.

For k>=0, unimodality of choose(k,j) puts the largest fair-binomial atom at j=floor(k/2). Set c_l=choose(2l,l)/4^l. The recurrence c_(l+1)=c_l(2l+1)/(2l+2) and c_0=1 prove c_l^2<=1/(l+1), since

    4(l+1)^3 - (2l+1)^2(l+2) = 3l+2 >= 0.

If k=2l, c_l<=1/sqrt(l+1)<=sqrt(2/(2l+1)). If k=2l+1, the largest atom is c_l(2l+1)/(2l+2)<=1/sqrt(l+1)=sqrt(2/(k+1)). For k=0 the actual atom is one and the asserted upper bound is sqrt(2), so the base case is valid. For K>=mu/2, sqrt(2/(K+1))<=2/sqrt(mu). No positivity of K is silently needed in this inequality.

An interval of real length <=w>=0 contains at most floor(w)+2 integers, regardless of endpoint inclusion. Splitting by K<mu/2 and then summing conditional atoms gives

    P(sum B_i in I) <= 4/mu + 2(floor(w)+2)/sqrt(mu).

The bad-event term is used once. This is uniform over all interval locations. It applies unchanged to an integer translate length(R)+sum B_i; averaging over cells needs no common center or common variance.

Boundary clarification: for m=0, mu=0 and the displayed inverse-mu estimates are not real-valued bounds. Use the trivial concentration bound one for that deterministic cell. In this application every good cell has m>=c^n>0, and every zero-slot cell is already in the exceptional-cell mass e_N. This is a necessary domain convention, not a defect in the good-cell estimate or endpoint.

For integer n>=1, 1/(2n+1)<=p_i<=1/2 gives

    mu>=2m/(2n+1)>=m/(2n).

Hence on m>=c^n, c>1,

    P(T in I | cell) <= 8n/c^n + 2(floor(w)+2)sqrt(2n/c^n).

Consequently the unconditional concentration function is at most e_N plus that expression. For w=3n^6, its polynomial factors are dominated by c^(n/2), so it tends to zero. No formula dividing by m or n is invoked at n=0; source inputs are N>=1 and n>=1. Statements about large n suffice for the all-N limit.

Abundance can also be entirely finite. At the first J=floor(N/6) block starts, let q_j(history)>=p=(2n)^(-3) be the conditional probability of the prescribed triple. Couple its success indicator by a fresh uniform threshold q_j; the threshold p indicators are independent Bernoulli(p) and lie below it. Conditional remaining block paths are sampled according to their actual finite laws. Equivalently, prove stochastic domination by induction of the two-branch finite transition recursion; no continuous uniform construction is required in Lean. Zero-mass histories may be filled arbitrarily. With nu=Jp>0, Var Bin(J,p)<=nu, so

    P(m(R)<c^n) <= P(Bin(J,p)<nu/2) <= 4/nu

once nu/2>=c^n. Taking c=3/2 works because F_n=Nat.fib(n+1) grows as phi^n, phi>3/2, uniformly for F_n<=N<F_(n+1). Also nu tends to infinity uniformly on these intervals. Raw block successes are not asserted independent. For J=0 the bound is replaced by one; this affects finitely many initial N only.

The geometric suffix estimate is separate and unchanged. For q=n^5 and p_n=1/(8n^3), (1-p_n)^q<=exp(-n^2/8). Since N<2^n, (3N+1)exp(-n^2/8) tends to zero. The estimate b_n=3n^5+n+3<=n^6 holds eventually. Concentration, abundance and the suffix estimates therefore hold for every sufficiently large N, not just a Fibonacci subsequence.

Supplementary exact rational diagnostics checked all atoms for 0<=k<=500, the induction polynomial for 0<=l<=500, and the complete coupling mass identity for m=1,...,4 and parameters in {0,1/10,1/4,1/2}. See finite-diagnostics.json. These support inspection only; the arguments above prove the universal assertions.
