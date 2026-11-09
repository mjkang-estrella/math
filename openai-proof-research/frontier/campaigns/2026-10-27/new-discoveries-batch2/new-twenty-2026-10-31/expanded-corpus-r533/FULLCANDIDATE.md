# FULLCANDIDATE, expanded-corpus-r533

Author: Claude Opus 5.5 discovery lane. Three author-complete ordinary proofs. No self-credit, no
independent review, no Lean, no mathematical program, enumeration or numerical test was run. Hand checks of
small cases were done on paper only. Root alone adjudicates.

Order is by the author's own assessment of how likely each is to survive a routine-exclusion attack:
347063 (strongest), 352303 (intermediate), 381964 (author recommends EXCLUDE AS ROUTINE).

---------------------------------------------------------------------------------------------------
# PART A. MathDB 347063: exact constants for the Split Smallest and Combine Smallest Zeckendorf games

Source: Li, Li, Miller, Mizgerd, Sun, Xia, Zhou, Deterministic Zeckendorf Games, arXiv 2006.16457v1
(only version on the arXiv listing read here), Conjecture 1.4, text page 3 and Section 4.

## A0. Literal binding, and a defect in the corpus literal

Source game (Definition 1.1): indices F_1=1, F_2=2, F_{i+1}=F_i+F_{i-1}. Start at n copies of F_1. Moves:
A1: F_1,F_1 -> F_2. Cons(i), i>=2: F_{i-1},F_i -> F_{i+1}. Split(2): F_2,F_2 -> F_1,F_3.
Split(i), i>=3: F_i,F_i -> F_{i-2},F_{i+1}. Game ends at the Zeckendorf decomposition.
Priorities (source section 1.2): Split Smallest = splits smallest first, then A1, then Cons smallest first.
Combine Smallest = A1, then Cons smallest first, then splits smallest first.

DEFECT: the corpus literal says the game "starts from the Zeckendorf decomposition of n". Read literally that
game has zero moves and no growth. The source starts from n copies of 1. I bind to the source game and flag
this for root; it is a corpus transcription error, not a mathematical claim of mine, and earns nothing.

SCOPE WARNING: the bare words "grows linearly" in the Theta(n) sense are already source Theorem 1.2, which
holds for every game (n-Z(n) <= moves <= 3n-3Z(n)-IZ(n)+1). If root reads the literal as Theta(n) only, this
target is SOURCE-OWN PUBLIC, credit 0. The content below is the existence and exact value of the limit
constants, which the source calls numerically apparent and does not prove.

## A1. Theorem

Let phi=(1+sqrt5)/2, psi=1/phi, and F_0:=1. Let SS(n) and CS(n) be the numbers of moves.

(a) SS(n) = phi^2 n + O(log^2 n).
(b) CS(n) = c n + O(sqrt(n) log n), where
    c = 1 + sum_{j>=1} (F_{2j}-1)/(F_{2j} F_{2j+2}) = 5/2 - phi + sum_{j>=2} 1/F_{2j} = 1.20648... .
Source Figure 2 plots against 1.20647n and Conjecture 1.4 says approximately 1.206. Source Figure 1 plots
against phi^2 n.

## A2. A general tail bound

Lemma T. From any position with c chips, all at indices <= L, every continuation has O(cL) moves.
Proof. A1 and Cons lower the chip count by 1 and splits keep it, so there are at most c combining moves. Let I
be the sum of the indices of all chips. A1 changes I by 0, Cons(i) by 2-i <= 0, Split(2) by 0, Split(i) for
i>=3 by -1. So the splits at indices >=3 number at most I <= cL. Each Split(2) uses two F_2, and F_2 chips
come from the at most c initial ones, from at most c A1 moves, and from Split(4), so Split(2) count is at most
(2c+cL)/2. Total O(cL). QED.

Also every move preserves total value n, so no chip has index L with F_L>n; L=O(log n).

## A3. Proof of (a)

Under Split Smallest, while any split or A1 is available, only those moves occur. So the game has a Phase 1
consisting of moves A1, Split(i) until a position with every a_i in {0,1}. Treat each as firing site i
(site 1 firing is A1; it loses two chips and puts one on site 2). Define weights
    w_j = j + 2 + psi (-psi)^j   (j>=1).
Then, using psi^2=1-psi:  -2w_1+w_2 = -1, -2w_2+w_1+w_3 = -1, -2w_3+w_1+w_4 = -1, and for i>=4,
-2w_i+w_{i-2}+w_{i+1} = -1. (Linear part j gives -1, constant part 2 gives 0, and the geometric part vanishes
because (-psi)^{-2} - 2 + (-psi) = phi^2-2-psi = 0; the three boundary equations are equivalent to
w(0)=w(1) and w(-1)=0 for the same formula with a=2, c=psi.)
Hence Phi=sum_j a_j w_j drops by exactly 1 at every Phase 1 move. With w_1=3-psi^2=phi^2, the number of Phase 1
moves is EXACTLY
    T(n) = phi^2 n - sum_j b_j w_j,   b_j in {0,1} the stable position.
(All w_j>0, so Phi>=0 and Phase 1 terminates, independently of the source's finiteness statement.)
Since only indices j <= O(log n) occur, and 0 < w_j <= j+3, sum b_j w_j = O(log^2 n). Phase 2 starts with at
most O(log n) chips at indices O(log n), so Lemma T gives O(log^2 n) moves. QED.
(Paper checks of the exact formula: n=2 T=1, n=3 T=1, n=4 T=3.)

## A4. Proof of (b): the exact state summary

Combining moves number exactly n-Z(n) (each lowers the chip count by 1 and splits keep it; this is also source
Lemma 3.3). So only splits S(n) need counting.

Definition. For even p>=4, a position is READY(p; N,Z,O) if a_p=N, a_{p+2}=O, a_{p+1}=0, all other chips form a
set Z of indices in [1,p-2] that has no repeats and no two consecutive indices, and there are no other chips.
By uniqueness of Zeckendorf representation Z is determined by its value L=sum_{z in Z}F_z, and L < F_{p-1}.
THE ENTIRE LOW STATE IS THE SINGLE INTEGER L.

Lemma R (rotation). Let READY(p;N,Z,O) with N>=5. The next moves form one MACRO and end in READY(p;N',Z',O')
with Z' the Zeckendorf set of L'= L+F_{p-2} if that is < F_{p-1}, else L+F_{p-2}-F_{p-1}. Non-wrap macros have
N'=N-3, O'=O+1. Wrap macros have N'=N-5, O'=O+2.

Proof. No A1 and no Cons is available and the smallest repeat is p (repeats in O are larger). So Split(p) fires,
giving chips p-2 and p+1. A pair (p,p+1) is then available and has lower priority index than (p+1,p+2), so
(p+1,p+2) never fires while a_p>=1. Now run the descent ADD(q), q even, starting at q=p-2, with the invariant
q+1, q+2 not in the current set.
 Case 1, q and q-1 not present: insert q. Stop.
 Case 2, q-1 present (so q absent): Cons(q) fires, leaving a chip at q+1, whose neighbours q and q+2 are empty.
   Stop.
 Case 3, q present: a repeat at q. It is the smallest repeat, so Split(q) fires, giving q-2 (or, if q=2, the chip
   1, which is absent because 2 was present) and a chip at q+1 whose neighbours q and q+2 are empty. Continue with
   ADD(q-2). Its invariant holds: q-1 was absent because q was present (Zeckendorf), and q has just been emptied.
   Later steps only add chips at smaller indices, so the chip at q+1 stays isolated. If q=2 stop.
 At the top level q=p-2, a chip produced at p-1 pairs with the pool: Cons(p) gives p+1 and then (p,p+1) gives
 p+2. Priorities are respected because in every position above exactly the listed move is the highest priority
 available: repeats occur at one index at a time, and consecutive pairs are exactly those listed.
 Case analysis at the top gives: no chip reaches p-1 iff p-2,p-3 are absent iff L<F_{p-3} iff L+F_{p-2}<F_{p-1}.
 Pool and output counts follow by adding moves, and value conservation fixes the final L'. QED

Lemma C (full cycle). Consecutive F_{p-2}, F_{p-1} are coprime, so L -> L+F_{p-2} mod F_{p-1} is a single cycle of
length F_{p-1}. Over any F_{p-1} consecutive macros: pool drops by exactly F_{p+2}, output rises by exactly F_p,
and the number of splits is exactly F_p-1.
Proof. a=F_{p-1} macros and b=F_{p-2} wraps (a F_{p-2}=b F_{p-1}). Pool drop 3a+2b=F_{p+2}, output a+b=F_p.
For splits: let d_q be the number of Split(q) and e_q the number of Cons(q) in the cascades, for even q <= p-2. Over
a cycle Z returns, so chips balance. Even q: chips in = chips out gives d_{q+2} = 2 d_q + e_q (with d_p replaced by
a). Odd q+1: e_{q+2} = e_q + d_q (with e_p replaced by b). Top: 2d_{p-2}+e_{p-2}=F_{p-1}, d_{p-2}+e_{p-2}=F_{p-2}, so
d_{p-2}=F_{p-3}, e_{p-2}=F_{p-4}. By descent d_q=F_{q-1}, e_q=F_{q-2} (bottom F_0=1; the chip balance at index 1 is
d_2=e_2 and holds). Total splits a + sum_{even q<=p-2} F_{q-1} = F_{p-1} + (F_1+F_3+...+F_{p-3}) = F_{p-1}+F_{p-2}-1 = F_p-1. QED

Paper checks: p=4 gives 13 fours to 5 sixes with 4 splits; p=6 traced by hand gives 34 sixes to 13 eights with
12 splits and 21 combines.

Level 2. After A1 moves, a_1 in {0,1}, a_2=floor(n/2). If a_1=1, Cons(2) then Cons(3) leave a_1=0 at no split cost.
From (0,K,0,N) with K>=5: Split(2), Cons(2), Cons(3), Cons(3) gives (0,K-5,0,N+2), one split, 5 twos to 2 fours,
matching F_2-1=1 and F_4=5.

Endgame lemma. From READY(p;K,Z,O) with K<=4 and O>=10, the game reaches READY(p+2;N',Z',O') with N' in [O-4,O+1],
O'<=2, Z' Zeckendorf within [1,p], in O(p) moves. Cases by K and by the Case 1, 2, 3 trichotomy for the chip at p-2:
K=0: Z unchanged. K=1: Z u {p}. K=2: Split(p); chip p+1 pairs (p+1,p+2) and then (p+2,p+3), so O drops by 2 and O'=1;
any chip reaching p-1 stays there as a low chip since a_p=0. K=3: Case 1 and Case 3 fire (p,p+1) leaving O+1; Case 2
gives (p-1,p) then two (p+1,p+2) and two (p+2,p+3), so N'=O-4, O'=2. K=4: Case 1 leaves Z u {p-2,p}, O+1; Cases 2 and
3 end at N'=O-1, O'=1. Level 2 endgame K=0..4 is the same small list and yields READY(4). Each Z' is Zeckendorf since
p-1 and p are never simultaneously present and p-2 absent when p-1 present.

Assembly. Value conservation at READY(p): N F_p = n - L - O F_{p+2}, so N_p = n/F_p + O(1) uniformly, with no
accumulation of errors. Number of full cycles at level p is N_p/F_{p+2}+O(1). So level p contributes
S_p = n (F_p-1)/(F_p F_{p+2}) + O(F_p). Let p* be the largest even p with F_p <= sqrt n; for p<=p* outputs are
>= sqrt(n)/O(1) >= 10 for large n so endgames apply. Sum over p<=p* gives c_S n + O(sqrt n), the tail of the infinite
series being O(sqrt n). At level p*+2 there are O(sqrt n) chips and indices O(log n), so Lemma T finishes with
O(sqrt n log n) moves. Finally sum_{j>=1} 1/(F_{2j}F_{2j+2}) telescopes to phi-3/2 by the Cassini identity, giving
the closed form of c. QED

## A5. Attempt to find a generic proof or a reduction, and what happened

1. Linear functional for Combine Smallest: any weights neutral on all Cons and A1 satisfy w_{i+1}=w_i+w_{i-1},
   so w is proportional to F_i and is also neutral on splits. So no potential counts splits in Combine Smallest.
   Part (a)'s method cannot apply to (b). This is why the rotation is needed.
2. Abelian sandpile: Part (a) is, in hindsight, a chip-firing odometer with an explicit potential. Generic chip-firing
   gives uniqueness but not the constant; the explicit w_j is needed. Part (a) alone is short, and root may regard it
   as a routine potential argument. I record that objection against (a).
3. Reduction to a source theorem: source Theorem 1.2 and Lemma 3.3 yield only Theta(n) and the combine count.
4. No general theorem known to me gives the constant in (b), which is transcendentally unusual (it contains the sum of
   reciprocals of odd-indexed Fibonacci numbers).

## A6. Limits on A
Prior art: NOT CHECKED BY ANY SEARCH on this target. All 3 native searches were spent before this route emerged. The
source is a Fibonacci Quarterly paper and there is follow-up Zeckendorf-game literature from the same group that I
did not read; a later exact result is possible. Final journal text not read. HOLD. Recommend a focused qualification
lane with fresh search budget before any further investment.

---------------------------------------------------------------------------------------------------
# PART B. MathDB 352303: extremal biharmonic index of trees, full conjecture

Source: Z. Lin, The biharmonic index of connected graphs, arXiv 2110.09931v1 (only version listed), Conjecture 5.3,
with BH(G)=n sum_{i>=2} 1/lambda_i^2. Literal matches source: n>=5, both bounds, both equality clauses.

## B1. Exact formula

For an edge e of a tree T let a_e,b_e be the sizes of the two components of T-e. For distinct edges e,f let alpha(e;f)
be the number of vertices of the component of T-e not containing f. Define
    N(T) = sum_e (a_e b_e)^2 + 2 sum_{unordered e != f} (alpha(e;f) alpha(f;e))^2.

Theorem 1. BH(T) = N(T)/n.

Proof. Let B be the oriented vertex-edge incidence matrix; L=BB^T and M=B^TB is positive definite on R^{E} because B has
full column rank for a tree. The nonzero eigenvalues of L are those of M, so sum 1/lambda_i^2 = trace(M^{-2}) = ||M^{-1}||_F^2.
For each e let x_e equal b_e/n on the a_e-side and -a_e/n on the other side, signs chosen so x_e differs by exactly 1 across e
in the orientation of e and is constant across all other edges. Then B^T X = I. Each x_e has zero coordinate sum, so X=BY and
Y=M^{-1}, hence X^TX=M^{-1}. Direct calculation: <x_e,x_e>=a_e b_e/n. For e != f, with outer sizes a=alpha(e;f), b=alpha(f;e) and
middle c=n-a-b, <x_e,x_f>=+-(ab/n^2)(-(n-a)-(n-b)+c)=-+ab/n. Square and sum. QED
Check against source Theorem 5.1: for S(a,b) with P=ab this gives N/n = n^2-2n+4P+(P+1)^2/n, the printed value.

## B2. Theorem

For every tree T on n>=3 vertices, BH(K_{1,n-1}) <= BH(T) <= BH(P_n), with equality on the left iff T is the star and on the
right iff T is the path.

Lower bound. a_e b_e>=n-1 with equality iff e is pendant, and alpha(e;f)alpha(f;e)>=1. So N(T)>=(n-1)^3+(n-1)(n-2), which is N
of the star, and equality forces every edge pendant, i.e. the star.

Upper bound. Let T be a non-path. Root T at a leaf and take a vertex v of degree >=3 at maximum depth. Then v has at least two
descending pendant paths of lengths p>=q>=1, and the rest R (containing v and its parent) has r>=2 vertices. Let T' be T with the
last vertex of the q-path moved to the end of the p-path, so (p,q) becomes (P,q-1), P=p+1>q. Put t=r-1>=1, so n=P+q+t.
Let Phi(m)=1^2+...+m^2, S=sum_{e in E(R)} s_e^2 where s_e is the size of the component of T-e not containing v.

Decompose N. R-R pairs: if an outer side avoids v it is inside R, otherwise it contains both paths and has size depending only on
R and p+q. So the R-R part is unchanged. Pairs (e in R, A_i): (s_e i)^2, giving S Phi(p) and similarly S Phi(q). Path edges with
outer size i: diagonal (i(n-i))^2; within a path i<i' gives (i(n-i'))^2; across paths (ij)^2. Hence
    N = C_R + 2S(Phi(p)+Phi(q)) + F(p)+F(q) + 2 Phi(p)Phi(q),
F(m)=sum_{k=1}^m (n-k)^2 U(k), U(k)=k^2+2Phi(k-1)=k(2k^2+1)/3.

Then N(T')-N(T) = 2S(P^2-q^2) + (n-P)^2U(P) - (n-q)^2U(q) + 2[P^2 Phi(q-1) - q^2 Phi(P-1)]. With n-P=q+t, n-q=P+t,
the t-free terms cancel identically (this is the fact that for t=0 the two shapes are the same path), leaving
    N(T')-N(T) = (P^2-q^2)(2S + (4/3) t P q) + t^2 (U(P)-U(q)) > 0.
Thus no non-path maximizes N among the finitely many n-vertex trees, so the path is the unique maximizer. QED

## B3. Attempt to find a generic proof or a reduction, and what happened

1. Laplacian coefficient monotonicity (Mohar 2007; Csikvari tree shift, recalled from memory, bodies not read here): sum 1/lambda^2 =
   (W/n)^2 - 2 c_{n-3}/n is a DIFFERENCE of two quantities that both increase toward the path, so coefficient monotonicity does not imply
   the result. I could not derive it from them.
2. Majorization: the path spectrum does not majorize that of the star; Schur-convexity goes the wrong way at the small eigenvalues.
3. One-parameter family: the same shift calculation appears to extend to the abstract sums sum (alpha alpha)^k, but only k=2 is spectral
   for the entrywise squares, so there is no spectral family containing the target. I did not prove the abstract family and I do not claim it.
4. The inverse edge-Laplacian entries are classical (Merris-type edge versions of the Laplacian, recalled from memory, body not read), and
   pendant-path shifting is the standard chemical-graph-theory tool. STRONGEST OBJECTION: a one-page combination of an old formula and an
   old transformation. No complete prior result-to-target bridge was found in the one search made, which returned no proof.

## B4. Limits on B
One search only, with excerpts; no novelty claim. Published final of Lin's paper, if any, unread; arXiv listing shows v1 only, no journal
reference. Companion Wei-Li-Yang arXiv 2110.02656 (Problem 6.3) not read.

---------------------------------------------------------------------------------------------------
# PART C. MathDB 381964: spectrum of the curvature-flow linearization on K_{n+1}

Source: Cushing, Kamtue, Liu, Muench, Peyerimhoff, Snodgrass, arXiv 2212.12401v1, Conjecture 3.5, eq. (9), Remark 3.1 (B' coefficients).
Final journal version Axioms 12 (2023) 577 returned HTTP 403: entire work closed to new deliveries, unread, see NEW-UNAVAILABLE.json.

## C1. Theorem. For every n>=2, the Jacobian of the normalized flow at P^s=(J-I)/n on K_{n+1}, on the tangent space T of non-lazy Markov
schemes, has eigenvalues -(n-1)/n with multiplicity C(n,2), -(n+3)/n^2 with multiplicity n, and -(n+3)/n with multiplicity C(n,2)-1,
counted algebraically, and P^s is asymptotically stable.

## C2. Proof. On the non-lazy Markov manifold, Sum_{z != x,y} p_yz = 1-p_yx and Sum_{z,w != x} p_xz p_zw = 1-a_x where a_x=(P^2)_xx, so eq. (9) becomes
    F_xy = (P^2)_xy - p_xy - 2 p_xy p_yx + 3 a_x p_xy.
For q in T let c_y=Sum_z q_zy. Then d(P^2)_xy=(c_y-2q_xy)/n and da_x=c_x/n, giving on T
    (Aq)_xy = c_y/n + 3c_x/n^2 - ((n+1)/n) q_xy - (2/n) q_yx.
This agrees with the printed Remark 3.1 coefficients B'. On T0 = {q in T : c=0}, A acts by -(n+1)/n - (2/n) transpose, so symmetric T0 has
eigenvalue -(n+3)/n, dimension C(n+1,2)-(n+1)=C(n,2)-1, and antisymmetric T0 has eigenvalue -(n-1)/n, dimension C(n+1,2)-n=C(n,2).
T/T0 is identified by q->c with {sum c=0}, dimension n, and column sums of Aq equal -((n+3)/n^2)c. So A is block triangular with the stated
spectrum, all eigenvalues are negative, and asymptotic stability follows as defined in the source. Essential-coordinate matrix of source
equation (20) is similar to A. QED

Paper check against source: n=2 gives -1/2,-5/4,-5/4; n=3 gives -2/3 with multiplicity 6 and -2 with multiplicity 2; n=4 gives -7/16 (4), -3/4 (6), -7/4 (5).

## C3. Generic-proof attempt: it succeeds, which is the objection
The block structure is forced: T is Ind_{S_n}^{S_{n+1}}(n-1,1) = (n,1)+(n-1,2)+(n-1,1,1), multiplicity free, so S_{n+1}-equivariance alone makes A a
scalar on each summand, and the proof is a one-vector evaluation of the source's own printed Jacobian at the uniform point.
AUTHOR RECOMMENDATION: EXCLUDE AS ROUTINE, credit 0. Strongest dissent: a deliberate printed conjecture with only numerics in the source, a true
exact all-n spectrum, and a cheap Lean endpoint. The final version is closed and unread and one search found nothing.
