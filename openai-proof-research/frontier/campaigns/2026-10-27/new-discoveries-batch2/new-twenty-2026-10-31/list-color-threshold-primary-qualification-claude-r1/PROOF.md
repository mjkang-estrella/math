# PROOF (independent reconstruction) -- MathDB 353552

Status at time of writing: written BEFORE opening inputs/author-candidate.md and
inputs/author-formal-plan.md. Only the disclosed mechanism sentence in TASK.txt
("per-colour miss counts and an averaged joint-miss bound, keeping the diagonal
and A'xB' pairs apart") and source arXiv 2202.03431v2 had been seen. All arithmetic
below was done by hand; no program, CAS or enumeration was used.

## Theorem
Let m >= 4 be an integer, t = m-1 >= 3, and let l >= 1 be an integer with
2l <= t^2. Then every m-assignment L of K_{2,l} has
    P(K_{2,l}, L) >= P(K_{2,l}, m) = m(m-1)^l + m(m-1)(m-2)^l.
Hence P_l(K_{2,l}, m) = P(K_{2,l}, m), and
    tau(K_{2,l}) <= max(4, ceil(1 + sqrt(2l))).

## Notation
Parts {x1,x2}, {y_1..y_l}. A = L(x1), B = L(x2), S_j = L(y_j), all of size m.
D = A cap B, d = |D|, k = m-d, A' = A\D, B' = B\D (both of size k, disjoint).
For a colour c: u_j(c) = 1 if c not in S_j, else 0; M(c) = sum_j u_j(c).
Constants: s = 1-1/t = (m-2)/t, q = 1+1/t, kappa = qs = 1-1/t^2.
Note 0 < s < 1 < q, 0 < kappa < 1, and kappa^{1/4} >= s because
kappa = s q >= s >= s^4.

Colour x1 with a in A and x2 with b in B (K_{2,l} has no x1x2 edge, so a = b is
allowed). The number of proper extensions is the product over j of |S_j \ {a,b}|:
    a = b  : prod_j (m-1+u_j(a)),
    a != b : prod_j (m-2+u_j(a)+u_j(b)).
Divide by t^l and define
    W(a,a) = prod_j (1 + u_j(a)/t)   >= 1 + M(a)/t   (a in D),
    W(a,b) = prod_j (s + (u_j(a)+u_j(b))/t) >= s^l    (a != b).
Then P(G,L)/t^l = sum_{a in D} W(a,a) + sum_{a != b} W(a,b), and the target is
P(G,m)/t^l = m + m t s^l.

## Step 1. Reduction to A'xB'
The off-diagonal pairs of AxB number m^2-d. A'xB' is off-diagonal with k^2 pairs;
the rest number m^2-d-k^2 and each has W >= s^l. Put Delta = sum_{a in D} M(a). Then
    P(G,L)/t^l - (m + m t s^l)
      >= d + Delta/t + sum_{A'xB'} W + (m^2-d-k^2) s^l - m - m t s^l
       = Delta/t + sum_{A'xB'} W - k - k(k-1) s^l,
using d-m = -k and m^2-d-k^2-mt = m-d-k^2 = k-k^2. If k = 0 we are done. Otherwise
it suffices to prove
  (I)  Delta/t + sum_{A'xB'} W >= k + k(k-1) s^l.

## Step 2. Counting misses
Let alpha_j = |A' \ S_j|, beta_j = |B' \ S_j|, delta_j = |D \ S_j|. Since
|A cup B| = m+k and |S_j| = m,
    alpha_j + beta_j + delta_j >= k   for every j,     Delta = sum_j delta_j.

## Step 3. The case k = 1
A' = {a}, B' = {b}. For each j, either u_j(a)+u_j(b) >= 1, giving a factor >= 1, or
u_j(a) = u_j(b) = 0, giving factor s and forcing delta_j >= 1. If e is the number of
j of the second kind, then W(a,b) >= s^e and Delta >= e, so by Bernoulli
Delta/t + W >= e/t + (1-1/t)^e >= 1. This is (I) for k = 1.

## Step 4. k >= 2: the averaged joint-miss bound
By AM-GM, sum_{A'xB'} W >= k^2 prod_j G_j, with G_j the geometric mean over A'xB'
of s + (u_j(a)+u_j(b))/t. With x = alpha_j/k, y = beta_j/k this mean takes the value
q on a fraction xy of pairs, the value 1 on a fraction x+y-2xy, and s on a fraction
(1-x)(1-y), so
    G_j = q^{xy} s^{(1-x)(1-y)},
which is nondecreasing in each of x, y. Let zeta_j = min(1, delta_j/k) in [0,1]. By
Step 2, x+y >= 1-zeta_j. Lowering x,y to x+y = w := 1-zeta_j (allowed since w >= 0):
(1-x)(1-y) = zeta_j + xy, so G_j >= kappa^{xy} s^{zeta_j}. With xy <= w^2/4 <= w/4 and
kappa < 1,
    G_j >= kappa^{(1-zeta_j)/4} s^{zeta_j}.
With Z = sum_j zeta_j in [0,l] and B(Z) := kappa^{(l-Z)/4} s^Z,
    sum_{A'xB'} W >= k^2 B(Z),    Delta >= k Z.
So (I) follows from Z/t + k B(Z) >= 1 + (k-1) s^l. As B(Z) >= s^{l-Z} s^Z = s^l, the
quantity kB(Z)-(k-1)s^l is nondecreasing in k, so k = 2 is the worst case:
  (III)  Z/t + 2 B(Z) >= 1 + s^l    for all real Z in [0,l].

## Step 5. Proof of (III) for t >= 3 and 1 <= l <= t^2/2
Put y = s^l, v = kappa^{l/4}, lambda = ln(kappa^{1/4}/s) > 0 and g = t lambda.
Then B(Z) = v e^{-lambda Z}. Since kappa = (1-1/t)(1+1/t),
    g = t[ (1/4) ln(1+1/t) - (3/4) ln(1-1/t) ]
      = sum_{n>=1} (1/n)(3/4 + (-1)^{n+1}/4) t^{1-n}
so g = 1 + 1/(4t) + ..., has positive coefficients, g > 1, g is decreasing in t, and
for t >= 3, g <= g(3) = (3/4)ln(4/3) + (9/4)ln(3/2) = 1.128058...

Case 1: y >= 1/(2g). Write p = l-Z in [0,l], so B = y e^{lambda p} >= y(1+lambda p).
Then Z/t + 2B - 1 - y >= (l/t + y - 1) + p(2 y lambda - 1/t) >= 0, the first bracket
by Bernoulli (s^l >= 1-l/t) and the second since 2 y lambda t = 2yg >= 1.

Case 2: y < 1/(2g). The convex function Z -> Z/t + 2v e^{-lambda Z} has minimum over
all real Z equal to (ln(2vg)+1)/g. So the left side minus 1+y is at least
    (ln(2vg)+1)/g - 1 - 1/(2g) = phi/g,   phi := ln(2vg) + 1/2 - g.
Since l <= t^2/2 and ln kappa < 0: ln v = (l/4) ln kappa >= (t^2/8) ln(1-1/t^2), and
t^2 ln(1-1/t^2) is increasing in t, so ln v >= (9/8) ln(8/9) = -0.132506... for t >= 3.
g -> ln g - g is decreasing for g >= 1, so with g in (1, g(3)]:
    phi >= ln 2 - 0.132507 + ln(1.128058) + 1/2 - 1.128058
         = 0.693147 - 0.132507 + 0.120497 + 0.5 - 1.128058 = 0.053079 > 0.
This proves (III), hence (I), hence the Theorem. []

## Corollaries
(a) If m >= max(4, ceil(1+sqrt(2l))) then m >= 4 and (m-1)^2 >= 2l, so
P_l(K_{2,l},m) = P(K_{2,l},m) (the inequality P_l <= P being trivial from the constant
assignment). As k0 = max(4, ceil(1+sqrt(2l))) >= 2 = chi(K_{2,l}), the definition
"smallest k >= chi with equality for every m >= k" gives tau(K_{2,l}) <= k0 = O(sqrt l).
(b) With source Theorem 4 (for l >= 16, tau(K_{2,l}) > floor((q/ln(16/7))^{1/2} + 1),
q = floor(l/4)), tau(K_{2,l}) = Theta(sqrt l). This is the literal of MathDB 353552.

## Sharp constant (not needed for the literal)
Fix theta < 4 ln 2. Then (III) holds for all large t and 1 <= l <= theta t^2. Case 1 is
unchanged. In Case 2, g -> 1 and v >= kappa^{theta t^2/4} -> e^{-theta/4}; if y is below
a small eps then phi' := ln(2vg)+1-g-gy -> ln 2 - theta/4 - eps > 0 uniformly, and if
y >= eps then l = O(t) so v -> 1 and y < 1/(2g) gives ln 2 - 1/2 > 0 in the limit. So
limsup tau/sqrt(l) <= 1/(2 sqrt(ln 2)). The source Lemma 12 with epsilon -> 0 gives the
matching liminf, because its first term in the max is O(m log m) = o(m^2) and its second
term is (m-1)^2 ln(4/(2-eps)) (1+o(1)). So tau(K_{2,l})/sqrt(l) -> 1/(2 sqrt(ln 2)).
