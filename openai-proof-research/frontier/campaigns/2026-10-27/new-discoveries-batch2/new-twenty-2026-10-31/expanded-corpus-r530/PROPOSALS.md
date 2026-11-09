# Complete ordinary arguments found in r530, with routine-argument attempts

Author: Claude Opus 5.5 in lane r530. None of this is independently reviewed. No programs, enumeration, CAS or Lean were
used. I recommend ZERO credit for all three items below, for the reasons stated. Root alone adjudicates.

Notation: chi is the Legendre symbol mod p, with chi(0)=0.

----------------------------------------------------------------------
## 352895 Totient congruence conjecture (Craig-Merca, arXiv 2112.05649v2, Conjecture 2)

Statement read in the source: when p>2 is prime there are no coprime integers A',B' with phi(A'n+B') = 0 mod p for all
n>=0. The source's standing convention is A,B>0, hence A',B'>0. For A'<=0 or B'<=0 the expression is not a positive
integer for all n>=0 except the trivial A'=0,B'=1, where phi(1)=1.

Theorem. If p is an odd prime, A,B>=1 and gcd(A,B)=1, then some n>=0 has p not dividing phi(An+B).

Proof. Dirichlet gives arbitrarily large primes in any reduced class. Throughout take primes larger than B and p.
Case 1: p does not divide A. By CRT the class c=B mod A, c=2 mod p is reduced mod Ap. Take a prime q in it. Then
  n=(q-B)/A>=0 and phi(q)=q-1=1 mod p.
Case 2: p divides A and B is not 1 mod p. Take a prime q=B mod A. Then q=B mod p, so q-1 is nonzero mod p.
Case 3: p divides A and B=1 mod p. Write A=p^e M with p not dividing M. By CRT choose a=2 mod p^e and a=1 mod M; a is a
  unit mod A because p is odd. Put b=B*a^{-1} mod A, also a unit. Take distinct primes q1=a and q2=b mod A. Then
  q1 q2=B mod A, so n=(q1 q2-B)/A is a nonnegative integer. Also q1-1=1 mod p and q2-1=2^{-1}-1=-2^{-1} mod p, both
  nonzero since p is odd. Hence phi(q1 q2)=(q1-1)(q2-1) is nonzero mod p. QED

Remark. The same two-prime choice gives M_p(A',B',G;phi)=0 for odd p when B'=1 mod p, so source Proposition 3.5's formula
would extend to all B' for odd p, conditional on source Theorem 1.1, which I did not audit.

Routine-argument attempt, and outcome. The attempt succeeded, which is the objection. Source Proposition 3.5 proves exactly
the B' not 1 mod p case by choosing A'n+B' prime via Dirichlet. Replacing "a prime" by "a product of two primes" closes the
one remaining case. That is a complete proof-level bridge from the source's own step, with no new invariant.
Strongest dissent: this is a deliberate printed conjecture and the authors wrote "our methods cannot address this
question"; it is a true statement, not a domain or wording correction; and no earlier proof was found in one bounded search.
RECOMMENDATION: zero credit, routine adaptation of the source's own Dirichlet step. Root may overrule.
Prior limit: a single search found nothing matching; the Springer record surfaced there could not be read (NETWORK-STOP.md).
Search 1's summary text wrongly says the paper does not treat phi; the actual body does (Section 3.2).
Lean: cheap. Literal in Nat: (p A B : Nat) (hp : p.Prime) (h2 : p != 2) (hA : 0<A) (hB : 0<B) (h : Nat.Coprime A B) :
exists n, not (p divides Nat.totient (A*n+B)). Needs mathlib's Dirichlet theorem on primes in progressions (I believe the
name family is Nat.setOf_prime_and_eq_mod_infinite and relatives; unverified here), CRT, Nat.totient_prime, Nat.totient_mul.
Specific imports only.

----------------------------------------------------------------------
## 372582 Quadratic lower bound for k-Pisano-Legendre primes (Andoyo, arXiv 2601.10561v1, Conjecture 4.1)

Definitions read: F_0=a, F_1=b, F_n=F_{n-1}+F_{n-2}; pi_p(a,b) is the least period mod p (Definition 2.6);
k=|L_1|-|L_{-1}|-|L_0| over one period (Definition 2.7); zeta(k) is the least odd k-PL prime.

Theorem. For integers (a,b) != (0,0) there is c in (0,1) with zeta(k) > c k^2 for every k in chi(a,b).

Proof. Let D=a^2+ab-b^2. D != 0 since sqrt 5 is irrational. Let E be {5} together with the odd primes dividing D; E is
finite. Fix an odd prime p not in E. Let r,s be the roots of x^2-x-1 in F_{p^2}, so rs=-1 and r != s. Write
F_n=A r^n+B s^n; then AB(r-s)^2=(b-as)(ar-b)=D, so A,B are nonzero. Let T=ord(r^2) and L=2T. Then r^L=1 and
s^L=(-1/r)^L=1, so L is a period and pi_p divides L. With S=sum over one period of chi(F_n), the sum over Z/L is (L/pi)S,
hence |S| <= |S_L|. Also s^n=(-1)^n r^{-n}, so with H=<r^2>:
  S_L = sum_{x in H} chi(Ax+B/x) + sum_{x in H} chi(A r x - (B/r)/x).
Both are of the form sum_{x in H} chi(A'x+B'/x) with A',B' nonzero.

Split case (5 is a residue, so r,s,A,B in F_p and H<=F_p^*, index m). H={y^m} is m-to-1, and multiplying by the square
y^{2m} gives sum_H = (1/m) sum_{y in F_p} chi(f(y)), f=y^m(A'y^{2m}+B'). As m divides p-1 and p is odd, A'y^{2m}+B' has
2m simple nonzero roots, so f is not a constant times a square and has 2m+1 distinct roots. Weil's bound for a quadratic
character of a polynomial (Lidl-Niederreiter Theorem 5.41; attributed, body not read here) gives |sum_{F_p}| <= 2m sqrt p,
so |sum_H| <= 2 sqrt p and |S| <= 4 sqrt p.

Inert case (5 a nonresidue). r^p=s, so r^{p+1}=-1 and r^2 lies in U={x: x^{p+1}=1}. H<=U has index m. Also B=A^p, and
A'=Ar, B'=-B/r satisfy B'=A'^p. With delta^2=5, y=(t+delta)/(t-delta) is a bijection from F_p union {infinity} to U, with
infinity mapping to 1. Then A'y^m+B'y^{-m}=P(t)/(t^2-5)^m where P=A'(t+delta)^{2m}+B'(t-delta)^{2m} is in F_p[t], and
chi of it equals chi(f(t)), f=P(t)(t^2-5)^m (t^2-5 is nonzero on F_p). The roots of P correspond under the Moebius map to
the 2m distinct solutions of zeta^{2m}=-B'/A', one possibly at infinity, so P has degree 2m or 2m-1 with simple roots, at
least one, none equal to +-delta. So f is not a constant times a square and has at most 2m+2 distinct roots, giving
|sum_{F_p}| <= (2m+1) sqrt p. Adding t=infinity and dividing by m: |sum_H| <= 3 sqrt p+1, so |S| <= 6 sqrt p+2.

Zeros. F_n=0 iff (r/s)^n=-B/A. With w=ord(r/s)=ord(-r^2), T divides 2w, so L divides 4w and |L_0| <= pi/w <= 4.
Hence |k|=|S-|L_0|| <= 6 sqrt p+6 for all p not in E.

Endgame. If |k|>=12 and p not in E then |k|-6>=|k|/2, so p>=k^2/144. If |k|<12 then k^2/200<1<p. Each p in E has one k-value
k_p. Choose 0<c<1/200 with c k_p^2 < p for all p in E. Every k-PL prime then satisfies p>ck^2, in particular zeta(k). QED

Routine-argument attempt, and outcome. The whole proof is the standard reduction of a character sum over a subgroup to a
full sum over F_p, applied to the two-term Binet form, then Weil. No step is specific to this conjecture.
Strongest dissent: the conjecture was posed on numerics only and I found no printed proof. The numeric constant 0.055 in
the source is consistent with an O(sqrt p) law.
RECOMMENDATION: zero credit, complete routine application of the Weil bound. Root may overrule.
Prior limit: one search only, no matching hit; a linear-recurrence character-sum bound of this type may exist in the
Niederreiter/Shparlinski literature, unread here.
Lean: expensive. mathlib, as far as I know, lacks Weil's bound for character sums of polynomials of unbounded degree; a
Stepanov-style proof or the hyperelliptic Riemann hypothesis would have to be built, plus the norm-one torus
parametrization. Not a realistic near-term target.

----------------------------------------------------------------------
## 381174 Balan-Wang Conjecture 5.2 (arXiv 1308.4718v1): refuted at k=3, given Komlos-Pintz-Szemeredi

Statement read: F=[g_1..g_{n+k}] is n by (n+k), all ||g_j||<=1, tau=min over n-subsets S of sigma_n(F_S). Conjecture 5.2:
there is C=C(k) with tau<=C/n^{k-1/2}.

Input, ATTRIBUTED AND BODY UNREAD: Komlos-Pintz-Szemeredi, A lower bound for Heilbronn's problem, J. London Math. Soc. 25
(1982): for all large N there are N points in the unit square with every triangle of area >= c0 log N / N^2.

Theorem (given that input). For k=3 no constant C exists.

Proof. Let N=n+3 and take p_1..p_N from KPS. Let x_j=(p_j,1)/||(p_j,1)|| in R^3, X=[x_1..x_N], Q=XX^T, which is positive
definite since the p_j are not collinear, and tr Q=N so lambda_max(Q)<=N. Put G=Q^{-1/2}X, so GG^T=I_3. Complete the rows of
G to an orthogonal N by N matrix, with F the remaining n rows. Each column of F has norm at most 1.
For T the complement of an n-subset S, orthogonality gives F_S^T F_S=I-G_S^T G_S and G_S G_S^T+G_T G_T^T=I_3, hence
sigma_min(F_S)=sigma_min(G_T). Also sigma_min(G_T)>=lambda_max(Q)^{-1/2} sigma_min(X_T)>=N^{-1/2} sigma_min(X_T).
Since ||(p,1)||<=sqrt 3, |det X_T|>=2 area(p_a,p_b,p_c)/(3 sqrt 3). All singular values of X_T are at most sqrt 3, so
sigma_min(X_T)>=|det X_T|/3. Thus tau>=c1 log N / N^{5/2}, and tau n^{5/2} tends to infinity. QED

Also proved here: for any rank-n admissible F whose kernel has orthonormal-row matrix G, a unit a attaining sigma=sigma_min(G_T)
gives c=G^T a in ker F, and F_S c_S=-F_T c_T yields sigma_min(F_S)<=sqrt k * sigma/sqrt(1-sigma^2) when sigma<1. So the
supremum of tau is within about a factor sqrt k of the Parseval quantity. The conjecture at k=3 is thus a Heilbronn-type
statement, and fails only by the KPS logarithm.

Separate zero-credit observation. The source's sentence that k=1 has upper bound C/n^{3/2} is false: the regular simplex
frame has tau=(n+1)^{-1/2}. Conjecture 5.2 itself is consistent with this at k=1, where the exponent is 1/2.

Routine-argument attempt, and outcome. The refutation is a complete short bridge from a classical theorem. Erdos's moment
curve only reaches the conjectured order, so the log factor from KPS is essential and I found no elementary replacement.
Strongest dissent: a precise printed conjecture is genuinely false, with no correction involved.
RECOMMENDATION: zero credit, complete application of KPS, and only a logarithmic violation. Root may overrule.
Prior limit: Shmalo 2607.06249v1 read for keywords only; it does not mention this conjecture, n+k or Heilbronn. Final
Balan-Wang journal version unread and not requested.
Lean: very expensive. The literal needs singular values and orthogonal completion, plus KPS, which rests on the
uncrowded-hypergraph independent-set theorem. Not in mathlib. Not a realistic target.
