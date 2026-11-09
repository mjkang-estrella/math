# FULLCANDIDATE: MathDB 353552, the list colour function threshold of K_{2,l}

Status: author-complete ordinary proof by the lane author (Claude Opus 5.5). NOT independently reviewed.
No acceptance, novelty or credit is claimed. Root alone adjudicates. No mathematical program, numeric test,
CAS, solver or Lean was used; every computation below was done by hand.

## 1. Target

Literal (corpus-bindings.json, id 353552): "tau(K_{2,l}) = Theta(sqrt l) as l -> infinity."
Source: Kaul, Kumar, Mudrock, Rewers, Shin, To, "On the List Color Function Threshold", arXiv 2202.03431v2,
Conjecture 5. Definitions used (source Section 1.2): P_l(G,m) is the minimum of P(G,L) over m-assignments L;
tau(G) is the smallest k >= chi(G) with P_l(G,m) = P(G,m) for all m >= k.
P(K_{2,l},m) = m(m-1)^l + m(m-1)(m-2)^l (source p.2).

The lower half is source Theorem 4, read in full: tau(K_{2,l}) > floor( (q/ln(16/7))^{1/2} + 1 ), q = floor(l/4),
l >= 16. The upper half is what was open. The follow-up (Kaul et al., arXiv 2207.04831v2, Involve 16 (2023))
proves tau(K_{2,n}) <= ceil((n+2.05)/1.24), restates the conjecture as its Conjecture 4, and says on p.4:
"it seems that a proof of Conjecture 4 will require a novel refinement of our approach or an entirely new approach."

## 2. Results

Theorem 1. Let m >= 4 and l >= 1 be integers with 2l <= (m-1)^2. Then P(K_{2,l},L) >= P(K_{2,l},m) for every
m-assignment L of K_{2,l}. Consequently P_l(K_{2,l},m) = P(K_{2,l},m) and
    tau(K_{2,l}) <= max{4, ceil(1 + sqrt(2l))}.

Corollary 2 (the literal). With source Theorem 4, tau(K_{2,l}) = Theta(sqrt l).

Theorem 3 (exact constant, stronger than the literal). tau(K_{2,l}) / sqrt(l) -> 1/(2 sqrt(ln 2)) as l -> infinity.

## 3. Notation and reductions

Let G = K_{2,l} with parts {x1,x2}, {y_1,...,y_l}. Fix an m-assignment; A = L(x1), B = L(x2), L_i = L(y_i).
For (a,b) in A x B the number of proper L-colourings with x1->a, x2->b is prod_i |L_i \ {a,b}| (a = b is allowed,
as x1, x2 are nonadjacent). So
    N(L) := P(G,L) = sum_{(a,b) in AxB} prod_i |L_i \ {a,b}|.
Let I = A cap B, c = |I|, p = m - c, A' = A \ I, B' = B \ I, so |A'| = |B'| = p; U = A cup B, |U| = m + p.

R0. If p = 0 then |L_i \ {a,b}| >= m-1 for a = b and >= m-2 for a != b, so N >= m(m-1)^l + (m^2-m)(m-2)^l = P.

R1 (lists inside U; this is Lemma 5 of 2207.04831, reproved here). If z in L_i \ U, replace z by some z' in U \ L_i
(which exists since |U| >= m and |L_i cap U| < m). For a,b in U the element z always survived and z' survives
unless z' in {a,b}, so no factor increases. Hence we may assume L_i is contained in U. Then M_i := U \ L_i has exactly p elements.

Put, for x in U, s_x := #{i : x in M_i}; for a != b, c_ab := #{i : a,b in M_i}. Note sum_{x in U} s_x = pl.

Assume m >= 3 and set a := 1/(m-1) in (0,1/2], and
    q := (m-1)/(m-2) = 1/(1-a),  tau_0 := m/(m-1) = 1+a,  r := 1 - a^2 = m(m-2)/(m-1)^2,  Q := q^l.
Dividing by (m-2)^l, each list contributes for a pair a != b a factor 1, q, or m/(m-2) = q^2 r according to whether
0, 1 or 2 of a,b are missing from it; and for a = b = x a factor q if x in L_i, and q*tau_0 if x is missing. Therefore
    (E1) for a != b:  g(a,b) := prod_i |L_i\{a,b}| / (m-2)^l = q^{s_a+s_b} r^{c_ab},
    (E2) for x in I:  prod_i |L_i\{x}| / (m-2)^l = Q tau_0^{s_x}.
Also P/(m-2)^l = mQ + m^2 - m =: T0. We must show T := N/(m-2)^l >= T0.

Identity: q r = tau_0.

## 4. The case p = 1 (all m >= 3; this is Lemma 6 of 2207.04831, reproved in this notation)

Each list misses exactly one colour, so c_ab = 0 for a != b. Write I, A' = {alpha}, B' = {beta}, c = m-1, w_x = q^{s_x} >= 1,
v = sum_{I} s_x, so s_alpha + s_beta = l - v and w_alpha w_beta = Q (1-a)^v.
T = Q sum_I tau_0^{s_x} + sum_{x != y in I} w_x w_y + W(w_alpha + w_beta) + w_alpha w_beta, with W = sum_I w_x >= c.
Bernoulli: sum_I tau_0^{s_x} >= c + a v, and (1-a)^v >= 1 - a v. So the Q-terms are >= Q(c + av + 1 - av) = mQ.
The rest is >= c(c-1) + 2c = m^2 - m. Hence T >= T0.

## 5. The case p >= 2 (the new part)

Assume p >= 2 and m >= 4, so a <= 1/3. Put v := sum_I s_x, t := v/p, n := l - t (0 <= t <= l since v <= pl),
x := a t, u := q^n >= 1, delta := r^{n/4}, Y := sum_I tau_0^{s_x}. Note Q = u q^t.

Term split of T by (E1),(E2):

(a) Diagonal: Q Y, with Y >= c + a v by Bernoulli.

(b) Pairs (alpha,beta) in A' x B' (p^2 of them). By AM-GM over these p^2 terms,
    K := sum q^{s_alpha+s_beta} r^{c_{alpha beta}} >= p^2 q^{E} r^{F},
    E = (1/p^2) sum (s_alpha + s_beta) = (s_{A'} + s_{B'})/p = n  (because s_{A'} + s_{B'} = pl - v),
    F = (1/p^2) sum c_{alpha beta} = (1/p^2) sum_i a_i b_i,  a_i = |M_i cap A'|, b_i = |M_i cap B'|, e_i = |M_i cap I|, a_i + b_i + e_i = p.
  Since a_i b_i <= (p-e_i)^2/4 <= p(p-e_i)/4 and sum_i e_i = v, F <= (pl - v)/(4p) = n/4. As r <= 1,
    (5.1)  K >= p^2 q^n r^{n/4} = p^2 u delta.
  This is the key step: it controls the joint-miss loss by an average, and it is exactly tight for the source's balanced assignment.

(c) Mixed pairs (alpha,x) and (x,beta), x in I. c_ab <= s_x gives g >= q^{s_alpha}(q r)^{s_x} = q^{s_alpha} tau_0^{s_x}. Summing,
    Mixed >= Y (Z_A + Z_B),  Z_A = sum_{A'} q^{s_alpha},  Z_B = sum_{B'} q^{s_beta}.
  By AM-GM, Z_A + Z_B >= 2 p q^{(s_{A'}+s_{B'})/(2p)} = 2 p sqrt(u).

(d) Pairs x != y in I: c_xy <= (s_x+s_y)/2 gives g >= (q^2 r)^{(s_x+s_y)/2} >= 1, so these contribute >= c(c-1).

Collecting, with m = c + p and (c+p)(c+p-1) - c(c-1) = 2pc + p^2 - p:
    T - T0 >= Q(av - p) + p^2 u delta + 2pc(sqrt u - 1) + 2 p a v sqrt u - p^2 + p.
Divide by p, use v = pt, x = at:
    (T-T0)/p >= Q(x-1) + p (u delta - 1 + 2 x sqrt u) + 1 + 2c(sqrt u - 1).
Here u delta = (q r^{1/4})^n >= 1, because (q r^{1/4})^4 = (1+a)/(1-a)^3 >= 1. So the coefficient of p is >= 0 and p >= 2 gives
    (T-T0)/p >= H := Q(x-1) + 2 u delta - 1 + 4 x sqrt u.
It remains to prove H >= 0.

If x >= 1: Q(x-1) >= 0, 2 u delta - 1 >= 1, 4x sqrt u >= 4, so H > 0.

Let x < 1. Since ln(1-x) <= -x and -ln(1-a) - a <= a^2 for a <= 1/2,
    (1-x) q^t <= exp(t(-ln(1-a) - a)) <= e^{a^2 t}.
Hence H >= u B - 1 + 4 x sqrt u, where B := 2 delta - e^{a^2 t}.

*Theorem 1 regime: a <= 1/3 and a^2 l <= 1/2.* Using ln(1-z) >= -z/(1-z), delta >= 1 - (n/4) a^2/(1-a^2) >= 1 - (9/32) n a^2.
Since 0 <= a^2 t <= 1/2, e^{a^2 t} <= 1 + 1.3 a^2 t (convexity, 2(sqrt e - 1) < 1.3). So
    B >= 1 - (9/16) n a^2 - 1.3 a^2 t >= 1 - 1.3 a^2 (n+t) = 1 - 1.3 a^2 l >= 0.35.
Using u >= 1 + n a (as u = (1-a)^{-n}, and -ln(1-a) >= a) and sqrt u >= 1,
    H >= (1+na)B - 1 + 4at >= -(9/16) n a^2 - 1.3 a^2 t + 0.35 n a + 4 a t
       = a[ n(0.35 - (9/16)a) + t(4 - 1.3 a) ] >= 0   (a <= 1/3).
This proves T >= T0. Together with R0 and Section 4 this proves the inequality of Theorem 1.

Since P_l <= P always (constant lists), equality follows. If 2l <= (m-1)^2 for m0 := max{4, ceil(1+sqrt(2l))} then the same holds for all m >= m0, and m0 >= 2 = chi(K_{2,l}). So tau(K_{2,l}) <= m0. QED Theorem 1.

Corollary 2. Source Theorem 4 gives tau(K_{2,l}) > floor((q/ln(16/7))^{1/2} + 1) with q = floor(l/4), which is >= c sqrt l for l >= 16 and an absolute c > 0. QED.

## 6. Proof of Theorem 3

Upper bound. Fix theta < 4 ln 2 and put B* := e^{-theta/4} - 1/2 > 0. Take a0 <= 1/3 small, and let m >= 1/a0 + 1 with l <= theta (m-1)^2, so a^2 l <= theta. The reductions above and the bound H >= uB - 1 + 4x sqrt u (for x<1) hold, and x >= 1 is immediate.
Since n <= l, delta >= exp(-(theta/4)/(1-a^2)); and since x < 1 gives a^2 t < a, e^{a^2 t} <= e^a. As a -> 0, 2 exp(-(theta/4)/(1-a^2)) - e^a -> 2 e^{-theta/4} - 1 = 2B*, so for a0 small B >= B*.
If u >= 1/B* then H >= 0. Otherwise n a <= ln u < C := ln(1/B*). Then delta >= 1 - n a^2/2 (for a^2 <= 1/2) and e^{a^2 t} <= 1 + 2 a^2 t, giving
B >= 1 - n a^2 - 2 a^2 t >= 1/2 for a0 small, since n a^2 <= a C and 2 a^2 t < 2a. Hence
    H >= (1+na)B - 1 + 4at >= -n a^2 - 2 a^2 t + n a/2 + 4 a t = a[ n(1/2 - a) + t(4 - 2a) ] >= 0.
So P_l(K_{2,l},m) = P(K_{2,l},m) for all m >= 1/a0 + 1 with l <= theta (m-1)^2. For l large, every m >= 1 + sqrt(l/theta) qualifies, so tau(K_{2,l}) <= 2 + sqrt(l/theta).

Lower bound. Source Lemma 12 (read in full): if t in N, m >= 3 and for some eps in (0,2),
t > max{ ln(eps/(4(m-2))) / (2 ln((m-2)/(m-1))), ln((2-eps)/4) / ln(1 - 1/(m-1)^2) }, then tau(K_{2,l}) > m for l >= 4t.
Fix theta' > 4 ln 2 and eps with ln(4/(2-eps)) < theta'/4. With t = floor(l/4) and l >= theta'(m-1)^2 the second term is at most ln(4/(2-eps))(m-1)^2 < t for large m, and the first is O(m ln m). So tau(K_{2,l}) > m when m - 1 = floor(sqrt(l/theta')) and l is large.
Letting theta up to and theta' down to 4 ln 2 gives the limit. QED.

Tightness check by hand: for the source's balanced assignment with l = 4t, in the notation above p = 2, c = m-2, s = l/2 on the four special colours, c_{alpha beta} = t, and
    T = cQ + 4 Q r^{l/4} + 4c q^{l/2} + c(c-1),
which multiplied by (m-2)^l equals the formula printed in source Lemma 9 term by term. Thus (5.1) holds with equality there, and T - T0 = Q(4 r^{l/4} - 2) + 4c(q^{l/2} - 1) - 2, whose sign change at r^{l/4} = 1/2 is the source of the constant 4 ln 2.
Consistency with published data (no computation by me): 2207.04831 Theorem 7 gives equality for (m,n) = (3, <=10), (4, <=24), (5, <=43) and failure for n >= 12, 27, 44; 4 ln 2 (m-1)^2 = 11.09, 24.95, 44.36.

## 7. Attempts to kill this candidate (required before proposing)

1. Generic bound. Wang-Qian-Yan tau(G) <= (|E|-1)/ln(1+sqrt 2) + 1, Thomassen |V|^10 + 1, and |E|-1 (cited in 2607.16810 as [4], body unread) are all linear or worse for K_{2,l}. No general sqrt|E| theorem exists in what I read; source Question 7 asks for exactly this and is open.
2. Reduction to a printed theorem. 2207.04831 Lemma 5 and Lemma 6 supply R1 and the p = 1 case, and I reproved both. Its Theorem 9 cannot reach sqrt l: it applies AM-GM once over all m^2 pairs, and the resulting geometric mean is dominated by (m-2)^l, while for l >> m the sum is dominated by the m(m-1)^l diagonal. Lemma 15 needs n <= (m+1/2) ln(m(1-eps)), i.e. n = O(m log m). The proof here is NOT that argument with an index changed: it keeps the diagonal and the A'xB' pairs separate, and pays the deficit pQ of missing diagonal terms by p^2 u delta. The joint-miss averaging (5.1), the linear-in-p reduction and H >= 0 are in nothing I read.
3. Classical theory. I found no reduction to a classical object (chromatic polynomial expansions and broken circuits give the linear bounds above; N(L) is a sum of products, not a permanent or determinant of a fixed matrix in any way I could use).
4. Parameter instance. I did not find a general K_{s,l} theorem containing this. The argument uses that a pair has only the two coincidence types a = b and a != b. I did not attempt s >= 3; a reviewer should test whether the same scheme gives K_{s,l} cheaply.
5. Weakness of literal versus proof. The literal Theta needs only Theorem 1 with any constant; the proof also gives the exact constant. The all-m explicit form and Theorem 3 are one family; do not count them separately.

Strongest objection, stated plainly: the proof is short and elementary: Bernoulli, AM-GM and one exact identity, on top of two lemmas already in the follow-up paper. The lower bound and its extremal assignment are the source's. A reviewer may judge the p >= 2 inequality to be a routine refinement of the follow-up's AM-GM, even though those authors said a novel refinement or new approach was needed. Strongest case for it: a deliberately posed conjecture, restated in a second paper with an explicit statement that its methods fall short, is settled in full, with the exact constant and a tightness explanation. Mechanism: a small exact state summary (missing counts s_x and the averaged joint-miss count) for a specific structured family.

## 8. Limits

Prior art is bounded: three standard searches (saved under searches/), the two source papers, and 2607.16810. No citation index or MathSciNet/zbMATH coverage. The journal final of 2202.03431 was not read (arXiv v2, 3 Aug 2023 read in full); the Involve final of 2207.04831 was not read. Of its arXiv v2 extracted text (96141 characters) I read characters 0-25431 (introduction, Lemma 5, Lemma 6 and its proof) and 43419-57900 (Lemma 15, its proof, the start of Corollary 16); characters 25431-43419 and 57900-end, which include the proofs of Theorem 7 and Theorem 9, were only pattern-scanned for sqrt, Conjecture 4 and Theta mentions. The source's Lemma 9-12 proof was read and its Lemma 9 formula matched by hand, not otherwise audited. |E|-1 bound paper [4] of 2607.16810 unread. No worldwide novelty claim. Independent review, significance, formal, paper and acceptance gates are all unpaid.
