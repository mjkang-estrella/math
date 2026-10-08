# H019 detectors: exact rank screen, missing aggregate operations

2026-10-08. Sol T3 proposer completed; full report retained in
H019-detectors-sol-raw.md with taskId. Native Astra
/root/h007_additive_relations independently reviewed it; root checked the
stronger rank proof, normalization and cost scopes. Paper-only findings,
no experiment admitted, no Lean theorem or new ECDLP improvement claimed.

## Exact separated counting: stronger, simpler rank obstruction

Let a cyclic group have odd prime order q, fix c nonzero and h=(q-1)/2.
Index nonzero negation orbits by {+-jc},1<=j<=h. The Boolean slice indicating
some signed relation between orbit i, orbit j and c is exactly the h-by-h
matrix with ones at |i-j|=1 and at(h,h), zeros elsewhere. Indeed
+-i+-j+-1=0 mod(2h+1) in this range gives precisely those cases.
On an ordinary prime-order EC subgroup, abscissae identify these negation
orbits. Relabelling for the proof is not an efficient procedure on unknown logs.

This is path adjacency with a last-vertex loop. For its leading zero-diagonal
path minors, D0=1,D1=0,Dk=-D(k-2). The final diagonal1 gives determinant
D(h-1)-D(h-2), hence +-1 for every h (h1 direct). Its rank is EXACTLY h over
EVERY field, including characteristic2 and characteristicq. This strengthens
the proposer's Fourier/deletion bound(q-3)/2 and removes its characteristic
restrictions. Root independently verified the orbit equation and recurrence.

Consequently a uniformly exact separated tensor representation
K(P,R,S)=sum_t u_t(P)v_t(R)w_t(S) needs at least h terms: fixing S=c yields
a matrix of rank at most the number of terms. The proposed literal evaluation
and aggregation of all terms cannot meet the sub-n^(3/2) gate at n~q^(1/3).
This is NOT a runtime lower bound for arbitrary implicit/adaptive circuits,
approximate tensors, randomized existence tests or coordinate methods.
Even a low-rank representation would need paid evaluation and localization;
an exact integer count detects existence, whereas a count modulo a field can
vanish through wraparound and needs a separate correctness mechanism.

## Random Fourier count: normalize and restrict the experiment

For three independent uniform length-n full-group lists WITH REPLACEMENT,
put Y_t=(sum_i omega^(ta_i))(sum_j omega^(tb_j))(sum_k omega^(tc_k)).
The exact count is n³/q +(1/q)sum_(t!=0)Y_t. With r iid uniform nonzero modes,
the unbiased estimator is n³/q +(q-1)/(qr)sum_sY_(t_s). Averaged over lists
and modes, its COMPLEX squared error is

    n³(q-1)(q-2)/(q²r).

The raw report missed the factor(q-1)/q. Derivation: E|Y_t|²=n³ and
E[Y_t conjugate(Y_u)]=0 for distinct nonzero t,u; subtract the conditional
mean's second moment n³/(q-1), then apply the estimator's scale.
For odd q>3, taking the REAL part gives

    n³(q-1)(q-3)/(2q²r),

using E[Y_t Y_u]=n³ exactly for u=-t and zero otherwise. Thus the claimed
constant RMS-accuracy count estimate needs r=Omega(q) when n³~q, even granting
free characters. This does not prove a lower bound for arbitrary decision
rules. Character evaluation on target-dependent points is itself unsupported.
Conditioning lists to nonzero points, signed abscissae, or distinct entries
changes the distribution; no exact formula above is imported into those cases.

## Divisor product and truncated norm: correct targets, no cheap operator

The divisor sum_i[A_i]-[S_A]-(n-1)[O], S_A=sum_iA_i, supports a Miller-style
function f_A. Product_j f_A(T-B_j) can detect an unsigned relation at T=-C_k
AWAY FROM ALL indexed potential poles {B_j,S_A+B_j}. Actual poles after
cancellation are insufficient: with A-list {A,D} and B-list {B0,B0+A},
T=B0+A can have one factor's zero cancelled by another's pole at O.
Treat those exceptional queries separately or charge justified restarts;
merely rejecting them is not a complete detector. After an ordinary zero,
one-list scan plus an A-dictionary can recover labels in soft-O(n) work.

The literal translation-grid evaluator performs n² point operations even if
f_A evaluation is free. Expanding all indexed zeros likewise does not meet the
gate. Compact straight-line description does not by itself provide a cheap
joint evaluator. This distinction is stated on
[Miller's primary manuscript page](https://crypto.stanford.edu/miller/), which
root read; no aggregate-evaluation theorem is imported from that abstract.

For split squarefree list polynomials A,B,C, the norm of S3 in
Fp[X,Y]/(A,B), reduced modulo C(Z), followed by gcd with C, is a correct
algebraic detector with paid sign/label recovery and verification. The proposed
dense first resultant has a quadratic-size X,Z representation; conventional
materialization misses the gate. Direct truncated norm remains a SPECIFIED
MISSING OPERATION, not a supplied algorithm. Dimension or degree alone does
not rule out every implicit implementation.

Root read the input/output statement of
[Bhargava et al., Theorem1.1](https://arxiv.org/pdf/2205.00342): explicit
coefficient vector and explicit evaluation points. It is not an existential
detector over an implicit Cartesian product. Root also read the opening
theorem/genericity discussion in
[van der Hoeven–Lecerf](https://www.texmacs.org/joris/resultant/resultant.pdf).
Its finite-field/generic-position and size assumptions require an actual
reduction; near-linear in the represented problem size is not automatically
subquadratic in list length. No applicable sub-n^(3/2) bound was supplied.

## Shared pair tables: compare the same many-target problem

A fixed-base table with m<=n² distinct pair sums has uniform-query hit rate m/q.
Its soft work m+Tq/m and memory m are already matched by fixed-base BSGS with
m baby steps and arithmetic-progression giant steps. Setup is charged on both
sides; known automorphism constants remain applicable. Optimize within1<=m<=q,
and retain per-target output/verification costs. Random scalar multiplication,
duplicates and failed queries cannot be free. Target-dependent first lists do
not inherit free cross-target reuse. No superior exponent or full-work constant
was established by replacing the BSGS table with pair sums. The independent
reviewer checked the construction and multiple-target discussion in
[Galbraith's primary lecture](https://www.math.auckland.ac.nz/~sgal018/ecc2015.pdf).
Root's separate web fetch timed out; that access limitation is not a source
verification. Root checked the elementary baby/giant cost derivation directly.

Best supported work remains the square-root reference for one ordinary target;
verified improvement NONE. No numerical experiment warranted by these four
cards. A concrete sub-n^(3/2) aggregate translation-product or truncated-norm
algorithm, with exceptions and recovery charged, would change that decision.
Independent Factory Fable and Grok H019 initial proposals remain separate.
