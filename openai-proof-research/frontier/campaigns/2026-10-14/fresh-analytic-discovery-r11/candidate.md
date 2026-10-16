# Sextic Salem Bernoulli convolutions: a finite seed criterion and the obstacle

Author: Myeongjin Kang (no affiliation). Prose licence: CC BY 4.0.
Campaign: fresh analytic discovery r11. Status: **UNRESOLVED** (target T not
proved, not disproved). Not counted; no PASS is claimed.

Frozen scope: `original-scope.md`, SHA-256
`143778fc32d5eb1f668b4b941ad1bd184b19c71b1bfb2792bee78b1effdd2bdd`.

## 0. Outcome in one paragraph

Target T asks whether the Bernoulli convolution at the reciprocal of the sextic
Salem number beta_6 = 1.40126836... (root of x^6 - x^4 - x^3 - x^2 + 1) is
singular. I did not prove or disprove T. I prove a finite-scale criterion
(Theorem S) for every Salem number of every degree: one algebraic integer A
whose unit-circle conjugates are small compared with its Fourier "action"
already forces Hausdorff dimension below one, hence singularity. For beta_6,
T therefore reduces to a single *seed problem*: find A in Z[beta_6] with
roughly L(A) - Lambda(A) >= 8 (exact form in Corollary S'). I also prove that
the trade-off in Theorem S cannot be improved beyond constants (Proposition
O1), and that product multipliers of the pinned quartic type at least double
the action per factor (Proposition O2). The remaining obstacle is to construct
the seed. For degree six, the pinned growth mechanism is critical rather than
supercritical, and numerical searches found no seed (Section 5, evidence only).

## 1. Setting and notation

Let beta > 1 be a Salem number of degree 2d >= 4. Its conjugates are beta,
beta^{-1}, and z_r^{+-1} = e^{+-i theta_r} for r = 1, ..., d-1, with theta_r in
(0, pi) distinct. Write K = Q(beta), O_K for its ring of integers, sigma' for
the embedding with beta -> beta^{-1}, and sigma_r for the embedding with
beta -> z_r. Because beta is a unit, beta^j A is in O_K for every A in O_K and
j in Z.

    nu = nu_{1/beta} = law of W = sum_{k>=0} eps_k beta^{-k},
    nu^(t) = E e^{itW} = prod_{k>=0} cos(t beta^{-k}),
    R = beta/(beta - 1) >= |W|,
    f(u) = -log|cos(pi u)|   (u not in 1/2 + Z),
    X_N = sum_{k=0}^{N-1} eps_k beta^{-k},  H_N = Shannon entropy of X_N
          (equal atoms merged).

f is even, 1-periodic, convex on each interval (n - 1/2, n + 1/2), and
f(u) >= (pi^2/2) ||u||^2, where ||u|| is the distance to Z
(use cos y <= exp(-y^2/2) for |y| <= pi/2).

**Seed data.** For A in O_K with A >= 1 (identity embedding), put
A' = sigma'(A), c_r = sigma_r(A), Delta(A) = sum_r |c_r|, L(A) = log(1/Delta),
and

    Lambda_L(A) = sum_{j<=0} f(A beta^j),
    Lambda_R(A) = sum_{j>=1} f(A' beta^{-j}),
    Lambda(A)   = Lambda_L + Lambda_R,
    gamma(A)    = inf_{j>=1} |cos(pi A' beta^{-j})|.

The sums converge (geometric tails, f(u) = O(u^2)); they are finite exactly
when no A beta^j (j <= 0) and no A' beta^{-j} (j >= 1) lies in 1/2 + Z. Then
gamma(A) > 0, because A' beta^{-j} -> 0.

### 1.1 beta_6 is a sextic Salem number

P6(x)/x^3 = y^3 - 4y - 1 with y = x + 1/x. The cubic has no rational root
(+-1 are not roots), so it is irreducible. Its roots lie in (-2,-1), (-1,0),
(2,3) (sign changes at -2, -1, 0, 2, 3). For the root y_0 > 2, x^2 - y_0 x + 1
has the real roots beta_6 > 1 and 1/beta_6. For the other two roots
x^2 - y x + 1 has a nonreal pair on the unit circle. The discriminant y^2 - 4
is negative under two real embeddings of Q(y_0), so it is not a square there
and x^2 - y_0 x + 1 is irreducible over Q(y_0). Hence [Q(beta_6):Q] = 6 and
beta_6 is a Salem number of degree six, d = 3. Numerically
beta_6 = 1.40126836794, theta_1 = 2.76630691720, theta_2 = 1.69819148530.

## 2. Theorem S: a finite seed criterion (proved)

The entropy and covering lemmas below follow the method of Cheng, Fang, Ma
and Zhang (arXiv:2610.12072v2, Lemmas 2.1 and 2.3), who treat quartic Salem
numbers. I reprove them for every degree. The only change is the
separation exponent 2(d-1). Lemma 4 is the trace-reflection step of the
pinned `sal:loss` (salem.tex, equations sal:trace, sal:taylor), written for
one multiplier and several circle pairs.

### Lemma 1 (separation of atoms)

Distinct atoms x != x' of X_N satisfy |x - x'| >= 2(beta-1) beta^{-N} N^{-2(d-1)}.

*Proof.* x - x' = 2u with u = sum_{k<N} d_k beta^{-k} != 0, d_k in {-1,0,1}.
The number v = beta^{N-1} u = sum_{l=0}^{N-1} d_{N-1-l} beta^l is a nonzero
algebraic integer, so its norm v sigma'(v) prod_r |sigma_r(v)|^2 is a nonzero
rational integer. Here |sigma'(v)| <= sum_{l>=0} beta^{-l} = R and
|sigma_r(v)| <= N. Hence |v| R N^{2(d-1)} >= 1, so
|u| >= beta^{1-N}/(R N^{2(d-1)}) = (beta-1) beta^{-N} N^{-2(d-1)}. QED

### Lemma 2 (entropy deficit from Fourier coefficients)

Let Q > 2, 0 < a <= 1/2, and let frequencies satisfy
pi <= xi_1, xi_{j+1} >= Q xi_j, xi_M <= beta^N, |nu^(xi_j)| >= a
(1 <= j <= M). Put Psi(a) = ((1+a)log(1+a) + (1-a)log(1-a))/2 >= a^2/2,
c_Q = (Q-2)/(Q-1), D = 2a/(pi c_Q (1 - (1+a)/Q)), B = aQ/((1-a)(Q-1)),
C_sep = 1 + (1+2R)/(2(beta-1)), C_{beta,Q}(a) = log[(2R+2+D) C_sep] + B. Then

    H_N <= N log beta - M Psi(a) + 2(d-1) log N + C_{beta,Q}(a).

*Proof.* nu is symmetric, so nu^ is real; choose sigma_j in {-1,1} with
E[sigma_j cos(xi_j W)] >= a. Let P(x) = prod_j (1 + a sigma_j cos(xi_j x)) and
F = log P. For t in [-1,1], concavity gives
log(1+at) >= ((1+t)/2) log(1+a) + ((1-t)/2) log(1-a); the right side is affine
and increasing in t, so E F(W) >= M Psi(a). Expanding P, a nonconstant
monomial whose largest chosen index is j has frequency at least
xi_j - sum_{i<j} xi_i >= c_Q xi_j, and the monomials with top index j have
total absolute coefficient a(1+a)^{j-1}. With |int_I e^{i w x} dx| <= 2/|w|,
for every interval I,
|int_I P - |I|| <= sum_j 2a(1+a)^{j-1}/(c_Q Q^{j-1} pi) <= D.
Also |F'| <= (a/(1-a)) sum_j xi_j <= B xi_M <= B beta^N.
Let eta = beta^{-N}, K = floor(W/eta), C_k = [k eta, (k+1) eta), U the union
of occupied cells (inside [-R-1, R+1]), Z_U = int_U P <= 2R + 2 + D,
q_k = Z_U^{-1} int_{C_k} P. For y in C_k, q_k >= (eta/Z_U) exp(F(y) - B), so
-log q_K <= N log beta + log Z_U - F(W) + B. Gibbs' inequality
H(K) <= E[-log q_K] gives H(K) <= N log beta - M Psi(a) + log(2R+2+D) + B.
Since W = X_N + eta W' with |W'| <= R, on {K = k} the atom X_N lies in an
interval of length (1+2R) eta. By Lemma 1 this interval contains at most
1 + (1+2R) N^{2(d-1)}/(2(beta-1)) <= C_sep N^{2(d-1)} atoms. Hence
H_N <= H(K) + H(X_N | K) <= H(K) + 2(d-1) log N + log C_sep. QED

### Lemma 3 (dimension from one finite scale)

For every N >= 1, dim_H nu <= H_N/(N log beta).

*Proof.* Group signs in blocks of length N: W = sum_{i>=0} beta^{-Ni} B_i with
B_i i.i.d. distributed as X_N, with atom probabilities p_b > 0. Fix
eps > 0. By the strong law, almost surely
-(1/n) sum_{i<n} log p_{B_i} -> H_N, so a.s. the prefix (B_0, ..., B_{n-1}) lies
for all large n in the set T_n of prefixes of probability at least
exp(-n(H_N + eps)); |T_n| <= exp(n(H_N + eps)). Each prefix determines W up to
an interval of length 2R beta^{-Nn}. Let U_n be the union of these intervals
and E = union_{n_0} intersection_{n>=n_0} U_n; nu(E) = 1. For
s > (H_N + eps)/(N log beta), the s-dimensional Hausdorff measure of
intersection_{n>=n_0} U_n is at most
liminf_n exp(n(H_N+eps)) (2R beta^{-Nn})^s = 0. Hence dim_H E <= s; let
eps -> 0. QED

### Lemma 4 (Fourier lower bound from one seed)

Let A in O_K, A >= 1, with Lambda(A) < infinity and Delta <= gamma/(4 pi),
gamma = gamma(A). Then for every integer n >= 0,

    -log|nu^(pi A beta^n)|
      <= Lambda_L + sum_{j=1}^n f(A' beta^{-j})
         + (2 sqrt2 pi / gamma) Delta sqrt(n Lambda_R) + (8 pi^2/gamma^2) n Delta^2
      <= Lambda + (2 sqrt2 pi / gamma) Delta sqrt(n Lambda) + 8 pi^2 n Delta^2/gamma^2.

*Proof.* nu^(pi A beta^n) = prod_{k>=0} cos(pi A beta^{n-k})
= prod_{j<=n} cos(pi u_j), u_j = A beta^j. For j >= 1, A beta^j is in O_K and
its trace is u_j + A' beta^{-j} + e_j in Z with
e_j = sum_r 2 Re(c_r z_r^j), |e_j| <= 2 Delta. Since f is even and
1-periodic, f(u_j) = f(v_j + e_j) with v_j = A' beta^{-j}. If |cos(pi v)| >=
gamma and |e| <= gamma/(2 pi), then |cos| >= gamma/2 on the segment, so
f'' = pi^2 sec^2 <= 4 pi^2/gamma^2 there, and
|f'(v)| = pi |tan(pi v)| <= (pi/gamma) sqrt(2 f(v))
(because 1 - c^2 <= -log c^2). Taylor's formula gives
f(v + e) <= f(v) + (pi/gamma) sqrt(2 f(v)) |e| + 2 pi^2 e^2/gamma^2.
Sum over 1 <= j <= n with |e_j| <= 2 Delta and Cauchy-Schwarz,
sum_j sqrt(f(v_j)) <= sqrt(n Lambda_R). QED

### Theorem S (seed criterion)

Let beta be a Salem number of degree 2d >= 4 and A in O_K a seed as in
Lemma 4. Let q >= 1 with Q = beta^q > 2, let M >= 1, n_max = q(M-1),

    a = min{ 1/2, exp(-Lambda - (2 sqrt2 pi/gamma) Delta sqrt(n_max Lambda)
                       - 8 pi^2 n_max Delta^2/gamma^2) },
    N = ceil(log_beta(pi A) + n_max).

If M Psi(a) > 2(d-1) log N + C_{beta,Q}(a), then dim_H nu_{1/beta} < 1; in
particular nu_{1/beta} is singular.

*Proof.* Take xi_i = pi A beta^{q(i-1)}, 1 <= i <= M. Then xi_1 >= pi, the
ratio is Q, xi_M <= beta^N, and |nu^(xi_i)| >= a by Lemma 4 (the bound is
increasing in n). Lemma 2 gives H_N < N log beta, and Lemma 3 gives
dim_H nu < 1. A measure of dimension below one gives full mass to a Borel set
of dimension below one, which is Lebesgue-null. QED

### Corollary S' (explicit form)

Choose M = 1 + floor(gamma^2/(16 pi^2 q Delta^2)). Then
8 pi^2 n_max Delta^2/gamma^2 <= 1/2, the cross term is at most
sqrt(Lambda/2), and a >= min{1/2, exp(-Lambda - sqrt(Lambda/2) - 1/2)}.
Since C_{beta,Q} is increasing in a, the hypothesis of Theorem S holds if

    2(L - Lambda) - sqrt(2 Lambda) > log(32 e pi^2 q / gamma^2)
                                     + log(2(d-1) log N + C_{beta,Q}(1/2)),

with N <= log_beta(pi A) + gamma^2/(16 pi^2 Delta^2) + 1 (and the case a = 1/2
is immediate). For beta_6: q = 3, Q = 2.7515..., R = 3.4921...,
C_sep = 10.95..., C_{beta_6,Q}(1/2) = 6.33... (recomputed by `verify.py`).
With gamma = 1/2 and log N about 30, the condition is roughly
2(L - Lambda) - sqrt(2 Lambda) > 14.1, for example L - Lambda >= 8 when
Lambda <= 2.

**Status of Theorem S.** Proved here, for every degree. For d = 2 it
specializes to the Cheng-Fang-Ma-Zhang criterion; there its hypothesis is met
deep in the pinned multiplier recursion (Lambda = o(L) by `sal:loss`). For
d >= 3 the theorem is new to this project; I found no statement of it in the
literature, but I do not claim literature novelty for the method.

## 3. The criterion is sharp up to constants (Proposition O1, proved)

**Proposition O1.** Let A be a seed with 2 Delta + |A'| beta^{-j_0} <= 1/2 for
some j_0 >= 1. Let
kappa = max 1/|sin(psi/2)| over the nonzero differences psi of the 2(d-1)
angles {+-theta_r} (finite, since the z_r^{+-1} are distinct). Then for
n > j_0,

    -log|nu^(pi A beta^n)| >= (pi^2/4) ( 2(n - j_0) sum_r |c_r|^2 - 4 kappa Delta^2 )
                             - (pi^2/2) |A'|^2 beta^{-2 j_0}/(beta^2 - 1).

*Proof.* With v_j = A' beta^{-j} and e_j as in Lemma 4, u_j = T_j - v_j - e_j
with T_j in Z. For j > j_0, |v_j + e_j| <= |A'| beta^{-j_0} + 2 Delta <= 1/2,
so ||u_j|| = |v_j + e_j| and
f(u_j) >= (pi^2/2)(v_j + e_j)^2 >= (pi^2/2)(e_j^2/2 - v_j^2), using
(x+y)^2 - x^2/2 + y^2 = (x/sqrt2 + sqrt2 y)^2 >= 0. Write
e_j = sum_alpha w_alpha e^{i phi_alpha j} over the 2(d-1) angles
phi_alpha in {+-theta_r}, with w = c_r for +theta_r and conj(c_r) for -theta_r.
Then

    sum_{j_0<j<=n} e_j^2 = (n - j_0) sum_alpha |w_alpha|^2
      + sum_{alpha != alpha'} w_alpha conj(w_alpha') sum_{j_0<j<=n} e^{i(phi_alpha - phi_alpha') j}.

Each geometric sum has modulus at most kappa, and
sum_{alpha != alpha'} |w_alpha||w_alpha'| <= (sum_alpha |w_alpha|)^2 = 4 Delta^2,
while sum_alpha |w_alpha|^2 = 2 sum_r |c_r|^2. Finally
sum_{j>j_0} v_j^2 <= |A'|^2 beta^{-2 j_0}/(beta^2 - 1), and every other factor
of the product has modulus at most one. QED

(Constants in O1 are not optimized; the point is the scaling: one seed yields
at most O((1 + Lambda) Delta^{-2}) usable frequencies above any fixed level,
so the e^{2(L - Lambda)} scale in Corollary S' cannot be improved beyond
constants by a better choice of frequencies along one seed orbit.)

## 4. Why the pinned construction does not supply a seed in degree six

### 4.1 Exact phase identity and action doubling (Proposition O2, proved)

For A_+ = A (beta^k - beta^{-k}) the phases satisfy the exact identity
u^+_j = u_{j+k} - u_{j-k} (pinned `sal:shift`). If A' = +-A, then
Lambda_R(A) = Lambda_L(A) - f(A), so Lambda(A) = 2 Lambda_L(A) - f(A); this is
exact and is the mirror (reflection) cost.

**Proposition O2.** Let A' = +-A, b = log_beta A, k >= b + h with h >= 1.
Suppose that |cos(pi u_i)| >= gamma for all i <= k, that
|cos(pi A' beta^{-i})| >= gamma for all i >= 1, and that
beta^{-h} < gamma/pi and 2 Delta < gamma/pi. For every eta in (0,1),

    Lambda_L(A_+) >= (1 - eta) [ Lambda_L(A) + sum_{i=1}^{k} f(u_i) ]
                     - (pi^2/(2 eta gamma^2)) beta^{-2h}/(1 - beta^{-2}),

and sum_{i=1}^{k} f(u_i) >= (1 - eta)(Lambda_R(A) - sum_{i>k} f(A' beta^{-i}))
- (pi^2/(2 eta gamma^2)) sum_{i=1}^k e_i^2.

*Proof.* f is convex on each branch (n - 1/2, n + 1/2), so
f(x + y) >= f(x) + f'(x) y whenever x and x + y lie in the same branch. If
|cos(pi x)| >= gamma then dist(x, 1/2 + Z) >= gamma/pi, so this holds for
|y| < gamma/pi. Also, by AM-GM,
|f'(x) y| <= (pi/gamma) sqrt(2 f(x)) |y| <= eta f(x) + pi^2 y^2/(2 eta gamma^2).
For j <= 0 apply this with x = u_{j+k} and y = -u_{j-k}, where
|u_{j-k}| <= beta^{b+j-k} <= beta^{-h+j}; the sum over j <= 0 of y^2 is at most
beta^{-2h}/(1 - beta^{-2}). Re-indexing, sum_{j<=0} f(u_{j+k}) =
Lambda_L(A) + sum_{i=1}^k f(u_i). For the second inequality, f(u_i) =
f(v_i + e_i) with v_i = A' beta^{-i}, |e_i| <= 2 Delta < gamma/pi, and
sum_{i=1}^k f(v_i) = Lambda_R(A) - sum_{i>k} f(v_i). QED

In addition, the argument of Proposition O1, applied to the indices
j_0 < i <= k, gives sum_{i=1}^k f(u_i) >= (pi^2/2)(k - j_0) sum_r |c_r|^2 - O(1),
and sum_r |c_r|^2 >= Delta^2/(d-1). So Lambda(A_+) >= c k Delta^2 - O(1): the
next exponent k is at most about Lambda(A_+) Delta^{-2}.

Together with the reflection identity, O2 says that one two-term factor at
least doubles the action, up to the factor (1 - eta)^2 and an additive term
of order k Delta^2. The pinned upper bound (`sal:loss`, (2+eta)(1+eta)) shows
that the doubling is exact to first order.

### 4.2 Exponent count (heuristic, labelled)

A two-term factor multiplies Delta by max_r |2 sin(k theta_r)|. In degree 2d
there are d - 1 angles. Simultaneous Dirichlet approximation gives
k <= X with max_r ||k theta_r/pi|| <= X^{-1/(d-1)}; for angles behaving
generically (unproved for Salem angles), nothing better than
X^{-1/(d-1) + o(1)} exists. The remark after Proposition O2 forces
k Delta^2 = O(1 + Lambda(A_+)), that is log k <= 2L + O(log Lambda(A_+)). Hence one factor gives at best

    L_+ <= L + (2/(d-1)) L + o(L),   Lambda_+ >= 2 Lambda (1 - o(1)).

* d = 2 (quartic): growth factor 3 against cost 2. This is supercritical, the
  pinned `sal:construction` margin (2.9 - 0.75 > 2.0301).
* d = 3 (beta_6): growth factor at most 2 against cost 2. This is critical,
  so the ratio Lambda/L cannot decrease to first order.
* d >= 4: growth factor 1 + 2/(d-1) < 2. This is subcritical.

The lower constraint k >= b + h (needed so that the perturbation u_{j-k} is
negligible) makes degree six worse. If the pigeonhole is restricted to
[K, X], the guaranteed simultaneous approximation is only about (K/X)^{1/2}.
Since K is about k_prev, which can be as large as e^{2 L_prev}, the
guaranteed growth falls to L_+ = 2L - L_prev, which is linear in the number of
steps. The quartic case avoids this through one-dimensional
continued-fraction dichotomies (the case analysis in `sal:construction`).
Those dichotomies have no two-dimensional analogue with the same exponent.
Seeds also start with ratio Lambda/L >> 1: a single factor has
Lambda of order k against L <= (1/2 + o(1)) log k. In the critical regime
the ratio therefore never reaches the threshold of Corollary S'.

### 4.3 Other linear combinations (heuristic, labelled)

I tested three variants on paper. None changes the exponent balance.

1. **Factor beta^k - eta with eta not a power of beta.** The new action is
   about Lambda(A) + Lambda(eta A) + k Delta^2. If eta is not a power of beta,
   eta A has circle conjugates of modulus about Delta and action below
   Lambda(A) only if it is itself a better seed. If eta is a unit whose circle
   conjugates have modulus one, then eta = +-beta^s up to finite index,
   because the unit rank is 3 and two circle moduli are fixed. That case is
   the two-term factor again.
2. **t shifted copies of one seed with signs.** For a palindromic or
   antipalindromic choice with t = 2s, the cost factor is 2s. The phase
   conditions number d - 1, with s free shifts in a range of size e^{2L}, so
   the growth is at most 1 + 2s/(d-1). For d = 3 this is 1 + s <= 2s, with
   equality only at s = 1. Without symmetry the growth is worse:
   1 + (t-1)/(d-1) against cost t.
3. **Pools of different seeds.** Matching the circle conjugates of two
   different seeds imposes 2(d-1) real conditions (modulus and phase) instead
   of d - 1 (phase only). Let P = e^{pL} seeds sit at level (Lambda, Delta).
   The best fixed point satisfies p(gamma - 1) = 2 - 4 gamma for growth
   1 + gamma in degree six, which is impossible for gamma > 1.
4. **Lucky approximations.** Khintchine-type luck gives at most an extra
   (1/4) log log k per step. This adds a summable correction to the ratio
   because L doubles at each step.

In every variant, degree six is at best critical. The ratio Lambda/L of a
seed is preserved to first order and starts far above one.

## 5. Numerical evidence (not proof)

Double-precision computations, reproducible with the scripts in `scripts/`;
outputs are in `evidence/`.

| experiment | beta | best ratio Lambda/L or L - Lambda |
|---|---|---|
| greedy product chain, 6 factors (k >= 2b+10) | beta_6 | Lambda/L: 70.4, 199, 695, 1404, 1971, 3429 (increasing) |
| greedy product chain, control | quartic P1 | Lambda/L: 13.8, 10.3 (decreasing; stops at the search cap) |
| annealed search, D in {-1,0,1}[x], deg <= 80, A != 0 | beta_6 | best L - Lambda = -5.33 (needed about +8) |

The search is crude (thousands of evaluations, no lattice reduction).
It does not rule out seeds; it only shows that none appears at small scale.

## 6. Exact obstacle

T would follow from Theorem S once the following finite problem is solved:

> **Seed problem for beta_6.** Find A in Z[beta_6] (A != 0, A >= 1) whose
> circle conjugates satisfy Delta(A) <= gamma(A)/(4 pi) and
> 2(L(A) - Lambda(A)) - sqrt(2 Lambda(A)) exceeds the right side of
> Corollary S'.

A certificate would need A and rational interval bounds for Lambda(A),
gamma(A), and Delta(A). Products prod(beta^{k_h} - beta^{-k_h}) cannot supply
such a seed by the first-order exponent count (Section 4.2): they double the
action while at best doubling L. Any successful seed must avoid the
reflection doubling, for example through multipliers with A' far from +-A
whose orbits still have small action on both sides. I found no such family.
Whether one exists is the open point; a negative answer would also require
Diophantine information about (theta_1, theta_2) that is not available.

## 7. Dependencies and novelty limits

* Pinned (accepted): `sal:main`, `sal:construction`, `sal:loss`,
  equations `sal:trace`, `sal:shift`, `sal:taylor` (salem.tex blob
  68552edd...; see source-contracts.md). Used only for comparison and for the
  exact shift and trace identities, which are reproved inline.
* Primary literature: Cheng-Fang-Ma-Zhang arXiv:2610.12072v2, Lemmas 2.1 and
  2.3 (method reproved above for general degree); arXiv:2610.09902v1;
  Marshall-Maldonado-Solomyak arXiv:2601.15035; Dajani-Kalle arXiv:1708.05544
  (withdrawn).
* New to this project: Theorem S for d >= 3, Corollary S' constants for
  beta_6, Propositions O1 and O2, and the critical-exponent diagnosis. Their
  novelty in the literature is not demonstrated.
* Not claimed: singularity, dimension drop, or absolute continuity for any
  Salem number of degree at least six.
