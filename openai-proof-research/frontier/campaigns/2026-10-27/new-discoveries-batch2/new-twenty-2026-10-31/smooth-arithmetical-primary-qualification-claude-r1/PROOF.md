# Independent reconstruction for MathDB 342017 (Claude Opus 5.5, by hand)

Written and saved BEFORE opening inputs/author-candidate.md. Only the mechanism
disclosed in TASK.txt (quasi-polynomial, alpha_(m-1), Stern-Brocot, ten-state
doubling transducer) was known to the reviewer. No program, enumeration, CAS or
solver was used for any step below; every identity was checked by hand.

Throughout, m,n>=1. N(m,n) := |SArith(P_{m,n})|.

## 0. Translation (source Definitions 1.1, 1.2, 1.3, 2.5; Lemma 2.6)

A zero label is impossible: 0 divides only 0, so all neighbours are 0 and by
connectivity every label is 0, contradicting gcd 1. So labels are positive.

With a_0 := 2 b_1, a_{m+1} := 0 the divisibility conditions are
a_i | a_{i-1}+a_{i+1} (1<=i<=m); smoothness 0<a_{i+1}<a_i forces a_{i+1} to be the
least residue of -a_{i-1} mod a_i (and a_{m+1}=0). Hence (a_i) is determined by
(a_1,b_1), likewise (b_i), and gcd(all labels)=gcd(a_1,b_1) since g|a_1,b_1 gives
g|a_i,b_i by the recursion. Conversely every coprime positive (a,b) yields, by the
same recursion, exactly one smooth structure. So (source Lemma 2.6)

  N(m,n) = #{ (a,b) coprime positive : F(2b,a)=m+1 and F(2a,b)=n+1 }.

Put x=a/b in Q_{>0}, ell(p/q):=F(p,q)-1. F is homogeneous, so

  N(m,n) = #{ x in Q_{>0} : ell(2/x)=m and ell(2x)=n }.     (1)

## 1. ell counts left letters

R(t)=t+1, L(t)=t/(1+t). Every positive rational is uniquely w(1) for a word
w in {L,R}* (reverse: p>q => R of (p-q)/q, p<q => L of p/(q-p); R maps to (1,oo),
L to (0,1); p+q strictly decreases).

Direct from Definition 2.5, for positive p,q: F(p+q,q)=F(p,q) (same x_3 onward)
and F(p,p+q)=1+F(p,q) (sequence p,p+q,q,x_4=-(p+q) mod q,...). F(1,1)=2.
Hence ell(1)=1, ell(Rt)=ell(t), ell(Lt)=1+ell(t), i.e.

  ell(t) = 1 + |path(t)|_L.                                  (2)

Also 1/L(t)=R(1/t), so inversion swaps letters. With (1):

  m-1 = |path(x/2)|_R ,  n-1 = |path(2x)|_L.                 (3)

## 2. Six doubling identities (checked as rational functions)

D(t)=2t, H(t)=t/2.
  D R = R R D;  D L L = L D;  D L R = R L H.
  H L = L L H;  H R R = R H;  H R L = L R D.
Terminal values: D(1)=2 (path R), H(1)=1/2 (path L), D L(1)=1, H R(1)=1 (empty).
Note path(M(u) y) = u path(y) for y>0, so the output prefix concatenates exactly.

## 3. Ten-state automaton

Machine A computes |path(2x)|_L reading path(x) left to right, started in D clean.
States A0=D clean, A1=D with pending L, A2=H clean, A3=H with pending R:
  A0: R->A0(+0); L->A1(+0).   A1: L->A0(+1); R->A2(+1).
  A2: L->A2(+2); R->A3(+0).   A3: R->A2(+0); L->A0(+1).
Terminal: A2 adds 1, others 0.
Machine B computes |path(x/2)|_R, started in H clean, is the letter-swap:
  B0: L->B0(+0); R->B1(+0).   B1: R->B0(+1); L->B2(+1).
  B2: R->B2(+2); L->B3(+0).   B3: L->B2(+0); R->B0(+1).
Terminal: B2 adds 1, others 0.

Reachable coupled states from 00 (ij = (Ai,Bj)); x marks A, y marks B:
  00: R->01 (1)      L->10 (1)
  01: R->00 (y)      L->12 (y)
  10: R->21 (x)      L->00 (x)
  12: R->22 (x y^2)  L->03 (x)
  21: R->30 (y)      L->22 (x^2 y)
  22: R->32 (y^2)    L->23 (x^2)
  03: R->00 (y)      L->12 (1)
  30: R->21 (1)      L->00 (x)
  32: R->22 (y^2)    L->03 (x)
  23: R->30 (y)      L->22 (x^2)
Terminal weights: 00,10,01,03,30: 1; 12,32: y; 21,23: x; 22: xy.
Exactly ten states. No zero-weight cycle. Each word gives exactly one x, so

  N(m,n) = [x^{n-1} y^{m-1}] G(x,y),  G = gf from 00 to termination.    (4)

## 4. Coefficient recursion

u=1/(1-x), v=1/(1-x^4). Z_s(k) = gf from state s with total y-degree k.
k=0: Z03=u, Z12=xu, Z22=x^3 v, Z23=x v, Z21=x, Z01=1, Z00=(3+x^2)u,
     Z10=(1+x)^2 u, Z30=(1+3x-x^2+x^3)u, Z32=xu.
For k>=1 (Z(j)=0 for j<0):
  e12(k)=[k=1]+x Z22(k-2);  e22(k)=[k=1]x+Z32(k-2);
  Z03(k)=u(Z00(k-1)+e12(k));  Z12(k)=u e12(k)+x u Z00(k-1);
  Z22(k)=v(e22(k)+x^2 Z30(k-1));  Z23(k)=x^2 v e22(k)+v Z30(k-1);
  Z21(k)=Z30(k-1)+x^2 Z22(k-1);  Z01(k)=Z00(k-1)+Z12(k-1);
  Z00(k)=u(Z01(k)+x Z21(k));  Z10(k)=Z00(k)-Z01(k);
  Z30(k)=Z21(k)+x Z00(k);  Z32(k)=[k=1]+Z22(k-2)+x Z03(k).

So every Z_s(k) is in Q(x) with denominator a product of (1-x) and (1-x^4).

Pole at x=1: by induction the order of Z00,Z10,Z30,Z03,Z12,Z32,Z22,Z23 at 1 is
at most k+1, of Z01,Z21 at most k. Let lambda_s(k)=lim (1-x)^{k+1} Z_s(k), and use
lim (1-x)v=1/4. Then lambda00(0)=4, lambda12(0)=1, lambda22(0)=1/4, lambda30(0)=4,
and for k>=1:
  lambda12(k)=lambda00(k-1), lambda22(k)=(1/4) lambda30(k-1),
  lambda30(k)=lambda00(k),
  lambda00(k)=lambda00(k-1)+lambda12(k-1)+lambda30(k-1)+lambda22(k-1).
Hence alpha_k:=lambda00(k) has alpha_0=4, alpha_1=2*4+1+1/4=37/4 and, for k>=2,
  alpha_k = 2 alpha_{k-1} + (5/4) alpha_{k-2},
whose solution is alpha_k=(15/4)(5/2)^k+(1/4)(-1/2)^k. In particular alpha_k>0.

Poles at zeta in {-1,i,-i}: u is regular there. Let p(k) bound the pole order of
all states except 22,23, and q(k) that of 22,23. p(0)=0, q(0)=1 and the recursion
gives by induction p(k)<=ceil(k/2), q(k)<=floor(k/2)+1. So the pole of Z00(k) at
zeta has order <=ceil(k/2)<=k<k+1 for k>=1, and is absent for k=0.

## 5. Theorem

For each fixed m>=1, with k=m-1: N(m,n)=[x^{n-1}]Z00(k). By partial fractions there
is n_0(m) such that on each residue class mod 4, for n>=n_0(m), N(m,n) is a
polynomial in n of degree exactly m-1, whose leading coefficient
alpha_{m-1}/(m-1)! is the same on every class. Therefore

  lim_{n->oo} N(m,n)/binom(m+n-1,n) = alpha_{m-1}
                                    = (15/4)(5/2)^{m-1}+(1/4)(-1/2)^{m-1}.

In particular N(m,n)=Theta_m(binom(m+n-1,n)) for every fixed m.

## 6. Hand checks against the source

m=1: Z00(0)=(3+x^2)u gives 3,3,4,4,... = source Theorem 3.1 exactly.
m=2: Z00(1)=u^2(3+x+4x^2+x^4)+u(x+x^2)+u x^6 v gives 3,8,17,25 and, for n>=4,
     9n-11+floor((n-3)/4) = source Theorem 4.2 exactly.
m=3: Z00(2)=A3 u^3+A2 u^2+A4 u^2 v+(x^4+x^6)u v with
     A3=3+5x+7x^2+2x^3+5x^4-x^5+x^6, A2=1+x+3x^2-x^3+x^4, A4=x^5+4x^6-x^7+2x^8.
     Values 4,17,48,95 at n=1..4 equal the source. For n>=5:
       N(3,n)=(47/4)n^2-36n+C, C = 209/4, 51, 213/4, 52 for n=1,2,3,0 mod 4.
     The source has 205/4, 51, 209/4, 52. The source formula's generating function
     minus ours is exactly -x^4/(1-x^2): the source undercounts by exactly 1 for
     every odd n>=5.
     Located error in source Table 2, the rows k=0 mod 4 with t=2 mod 4 and t=3 mod 4:
     F(4a,4a-t)=F(t,4a-t) and the general reduction needs t>=4. Direct: t=2 gives
     F=4l-2 and n-5=K+4(l-2); t=3 gives F=4l and n-7=K+4(l-2); the table's general
     rows would give n-6 and n-8. True minus table is +1 iff n=1 mod 4 (t=2) or
     n=3 mod 4 (t=3), matching the gf difference. Explicit missing structure at
     n=5: k=4,l=2,t=2, primitive a=(3,2,1), b=(5,4,3,2,1): 3|2+10, 2|3+1, 1|2,
     5|6+4, 4|5+3, 3|4+2, 2|3+1, 1|2. So N(3,5)=166, not the printed 165.
     This correction earns no credit.

## 7. A one-page proof of the bare growth (adversarial; see REVIEW.md)

Lower bound from source Lemma 2.7 alone: (a,b)->(a,b+2a) gives
F(2a,b+2a)=1+F(2a,b), F(2b+4a,a)=F(2b,a), so n+1 with m fixed; (a,b)->(a+2b,b)
gives m+1 with n fixed. Both preserve coprimality; the images are disjoint since
A>2B and B>2A cannot both hold; start at (1,1) with m=n=1. Hence
N(m,n) >= binom(m+n-2,m-1).

Upper bound from the two 2-state machines of Section 3 only. Let w=path(x), B=m-1,
A=n-1. (i) Every maximal R-run followed by an L adds at least 1 to B: inspect the
B-state before the run, which is B0, B2 or B3 because the previous letter is L or
the run is at the start. So w has at most m maximal L-runs. (ii) #R(w)<=2B+1, so
the sequence of R-run lengths has at most C_m possibilities. (iii) For fixed
R-pattern and all other L-run lengths, raising one L-run length q>=1 by 2 returns
the A-machine to the same state and adds at least 1 to A; so at most 3 lengths are
possible for one chosen run given the rest. (iv) q_i<=2n+2 for each run. Hence
N(m,n)<=C'_m n^{m-1}. Together: Theta_m(n^{m-1}).

## 8. Readings

"Same rate": the source says, immediately before Conjecture 1.4, that in each of
the proved cases the count "grows on the order of a polynomial of degree m-1 in n".
So the literal is Theta for fixed m, n->oo. Asymptotic equivalence with ratio 1 is
false already at m=1 (limit 4). Uniform two-variable Theta is false: N is symmetric
and N(m,1)=4 for m>=3 while binom(m,1)=m. Also alpha_{m-1}->oo, so even the
symmetric comparison binom(m+n-2,m-1), which is a lower bound, fails uniformly.
