# PROOF.md — independent reconstruction for MathDB 344875

Written BEFORE opening inputs/author-FULLCANDIDATE.md or inputs/author-DORMANT-FORMAL-PLAN.md.
Disclosure: TASK.txt disclosed the mechanism (level-window count; two-adjacent-position
construction; the value beta_k). This is independent verification, not independent invention.
All arithmetic below is by hand. No program, enumeration or solver was used.

Reviewer: Claude Opus 5.5. Credit 0. Root alone adjudicates.

## 0. Setting (source arXiv:1912.05775v2, read in text and viewed on pp. 1, 2, 9-12)

S_n(k): hub a_0 and n arms a_{i,1},...,a_{i,k}; a_0 ~ a_{i,1}, a_{i,j} ~ a_{i,j+1}.
Level of a_{i,j} is j; hub has level 0. A locating q-colouring gives every vertex a distinct code
(d(v,C_1),...,d(v,C_q)). The source p.1 writes "k-coloring" without the word proper, but proper
colourings are used in its proofs (p.5 "it cannot be color 1 because u is adjacent to v and c(v)=1";
p.11 the sets (A u {p}) \ {c(x_i)}; Theorem 5.2's y in {..}-{x}). Below the LOWER bound is proved for
arbitrary (even improper) colourings and the UPPER bound constructs proper surjective colourings,
so the leading-constant theorem holds under either convention.

Notation for fixed k>=2: l=floor(k/2), u=ceil(k/2), beta_k=(l^l u^u)^(1/k).

## 1. Theorem

For every fixed k>=2 there are constants C_k, n_k such that for all n>=n_k
    beta_k n^(1/k) - (u-1) <= chi_L(S_n(k)) <= beta_k n^(1/k) + C_k.
The lower bound holds for all n>=2. Consequently chi_L(S_n(k)) = (1+o(1)) beta_k n^(1/k) for fixed k.
Corollary: for every k>=4, beta_k < ((k-1)/2) 4^(1/k), so Conjecture 5.1 is false for every k>=4.

The o(1) is for k fixed and n->infinity. That is the only tenable reading: source p.9 says "if we fix k",
and source Corollary 4.1 gives chi_L = ceil(log_3(n/4))+3 once k>=2ceil(log_3(n/4))+4, which is
incompatible with the printed formula uniformly in k.

## 2. Window lemma (exact distance from a first-level vertex)

Let c be any q-colouring and h=c(a_0). For a colour t that occurs let D_t = min level of a vertex of
colour t; D_h=0. Let W_j={t: D_t=j}, w_j=|W_j| (1<=j<=k). Then sum_{j=1}^k w_j <= q-1.
Fix arm i, write x_j=c(a_{i,j}). For t in W_j with j>=1:
 - if x_j=t then d(a_{i,1},C_t)=j-1;
 - else if j<k and x_{j+1}=t then d(a_{i,1},C_t)=j;
 - else d(a_{i,1},C_t)=j+1.
Proof. All vertices of colour t have level >=j. A colour-t vertex at level m in arm i is at distance
|m-1|=m-1 from a_{i,1}; one at level m in another arm is at distance 1+m>=1+j; the hub does not have
colour t. Case 1: m=j in arm i gives j-1, the minimum possible. Case 2: x_j != t and x_{j+1}=t gives j, and
nothing closer exists since arm-i occurrences have m>=j+1 and other arms give >=1+j. Case 3: arm-i
occurrences have m>=j+2, giving >=j+1; and since D_t=j while x_j != t, a level-j vertex of colour t lies in
ANOTHER arm, at distance exactly 1+j. So the same-arm position of the depth-D_t vertex is handled: it can only
occur in case 1. []
For the hub colour: d(a_{i,1},C_h)=0 if x_1=h, else 1 (the hub is at distance 1). Proper colourings have x_1 != h.

Reduced tuple. Put r_1=x_1 (which lies in W_1 u {h}), and for j>=2 put r_j=x_j if x_j in W_j u W_{j-1},
otherwise r_j=*. By the lemma the code of a_{i,1} is a function of (r_1,...,r_k) alone: a colour in W_j reads
only positions j and j+1, and any x_m in W_{j'} with j'<=m-2 or x_m=h (m>=2) is invisible.

## 3. Lower bound

A locating colouring gives the n vertices a_{i,1} distinct codes, so the n reduced tuples are distinct:
    n <= s_1 s_2 ... s_k, s_1=w_1+1, s_j=w_j+w_{j-1}+1 (j>=2).
Odd positions: s_1+s_3+... = (w_1+1)+(w_2+w_3+1)+(w_4+w_5+1)+..., disjoint w's, u terms, so sum <= (q-1)+u.
Even positions: s_2+s_4+... = (w_1+w_2+1)+(w_3+w_4+1)+..., disjoint w's, l terms, so sum <= (q-1)+l.
Both hold in both parities of k: for k odd the odd chain ends at w_k and the even chain at w_{k-1}; for k even the
odd chain ends at w_{k-1} and the even chain at w_k. AM-GM on each chain:
    n <= ((q-1+u)/u)^u ((q-1+l)/l)^l <= (q-1+u)^k/(u^u l^l),
hence q >= beta_k n^(1/k) - (u-1). []

The extremal problem: maximise om_1 prod_{j=2}^k (om_{j-1}+om_j) over the simplex; value 1/(l^l u^u).

## 4. Construction

Data: integers w_1,...,w_k>=0 with w_1>=3 and w_j+w_{j-1}>=1 (j>=2). Colours {h} disjoint-union W_1..W_k,
|W_j|=w_j. Let T be the set of tuples (x_1,...,x_k) with x_1 in W_1 and, for j>=2,
    x_j in (W_j u W_{j-1} u {h}) \ {x_{j-1}}.
So colours of W_j occur only at positions j and j+1, and adjacent colours differ, and x_1 != h.

Count: at each j>=2 at least w_j+w_{j-1} choices remain, so |T| >= N_0 := w_1 prod_{j=2}^k (w_j+w_{j-1}).

Coverage. Call F subset T covering if every t in W_j (each j) has an arm x in F with x_j=t.
T itself covers: x_{j-1} is never in W_j so t is available at level j, a prefix exists since W_1 is nonempty and
h or W_j u W_{j-1} is always available, and any x_{j+1} != t exists because h != t.
A covering subfamily of size <= sum w_j exists, so every n with sum w_j <= n <= |T| admits a covering F, |F|=n.

Colouring: c(a_0)=h; arm indexed by x in F receives c(a_{x,j})=x_j. Proper and uses all colours.

Claim: c is locating on S_{|F|}(k). Let t in W_j; by coverage D_t=j exactly.

(a) Level is decoded. For u at level p (p=0 is the hub) and any t in W_1: d(u,C_t) <= p+1, since a level-1 vertex of
colour t exists (via hub distance p+1, or shorter if it is on u's arm). An arm contains at most two colours from
W_1 (positions 1,2), and w_1>=3, so some t in W_1 is absent from u's arm; then every colour-t vertex lies in another
arm at level>=1, so d(u,C_t)>=p+1. So p = max_{t in W_1} d(u,C_t) - 1. In particular two vertices with equal
codes have the same level, and the hub (the unique level-0 vertex) is separated from all others.

(b) Arm is decoded at level p>=1. Let u=a_{x,p}, t in W_j. Since x_j=x_{j+1}=t is impossible (proper):
   x_j=t       => d(u,C_t)=|p-j|;
   x_{j+1}=t   => d(u,C_t)=|p-j-1|;
   otherwise   => d(u,C_t)=p+j.
Each uses that other-arm occurrences are at distance >=p+j, and p+j >= |p-j| and p+j >= |p-j-1| (p,j>=1).
The three values are pairwise distinct for p,j>=1: |p-j| and |p-j-1| have opposite parity; |p-j|<=p+j-2;
|p-j-1|<=p+j-1. So from p and the code one reads, for every non-hub colour, exactly where it sits in the arm. Every
position not holding a non-hub colour holds h. Hence x is determined, and distinct arms get distinct codes. []

## 5. Parameters and the leading constant

k=2u even: w_odd=m, w_even=0. Then w_1=m, w_{j}+w_{j-1}=m, N_0=m^k, q=1+um.
k=2l+1 odd (u=l+1): w_{2r+1}=(l-r)m (0<=r<=l), w_{2r}=rm (1<=r<=l). Then w_1=lm,
w_{2r-1}+w_{2r}=um, w_{2r}+w_{2r+1}=lm, so N_0=(lm)^u(um)^l and sum w_j = u*lm, q=1+ulm. w_k=0.
With gamma_k=u (k even), ul (k odd): (q-1)^k/N_0 = gamma_k^k m^k/N_0 = l^l u^u in both cases.
Requires m>=3 (w_1>=3) in even case, m>=3 in odd case as lm>=3 (l>=1).

For large n take the least m>=3 with N_0(m)>=n. If m>3, N_0(m-1)<n gives gamma_k(m-1) < beta_k n^(1/k), hence
q=1+gamma_k m < beta_k n^(1/k)+gamma_k+1. For n>=n_k also n>=sum w_j, so a covering F with |F|=n exists. []

Monotonicity (source Lemma 5.1) is NOT needed.

## 6. Refutation inequality

Odd k=2l+1, l>=2: beta_k^k = l^l (l+1)^(l+1), printed^k = l^k*4 = l^(2l+1)*4.
beta_k^k < printed^k iff (1+1/l)^(l+1) < 4. At l=2 it is 27/8; (1+1/x)^(x+1) decreases in x. True.
Even k=2u, u>=2: beta_k=u, printed=(u-1/2) 4^(1/k), beta^k<printed^k iff (1+1/(2u-1))^(2u) < 4. At u=2: (4/3)^4=256/81<4,
and the sequence (1+1/x)^(x+1) decreases. True. Equality occurs exactly at k=2 (x=1) and k=3 (l=1), where the
source Theorems 5.2, 5.3 confirm the formula. beta_4=2 versus printed (3/2)sqrt(2)=2.1213...

## 7. The k=4 witness on its own

Sets A,B of size b>=3, colour h. Family x_1 in A; x_2 in (A u {h})\{x_1}; x_3 in B; x_4 in (B u {h})\{x_3}: exactly b^4 tuples.
Sections 4(a),(b) apply (W_1=A, W_3=B, W_2=W_4=empty; level 3 restricted to B is a subfamily and still covers).
So chi_L(S_{b^4}(4)) <= 2b+1, ratio to the printed formula -> 2 sqrt(2)/3 = 0.9428..., a fixed value below 1. This uses only
the construction; the lower bound is not needed to refute k=4.

## 8. Printed constant reconstructed as an allocation

Setting om_1=...=om_{k-1}=1/(k-1), om_k=0 in the extremal functional gives
(1/(k-1)) * (2/(k-1))^(k-2) * (1/(k-1)) = (1/4)(2/(k-1))^k, i.e. exactly q = ((k-1)/2)(4n)^(1/k).
So the printed formula equals the uniform allocation over levels 1,...,k-1. It is optimal for k=2,3 and suboptimal for k>=4.
This is the reviewer's reconstruction: the source gives no derivation (p.10: "We end this section with the following conjecture.").
