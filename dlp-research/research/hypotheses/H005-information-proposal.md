# H005 I1: arithmetic steering of an inverse binary walk

Status: speculative, low-priority independent proposal; no experiment approved.
Proposer: native Astra `/root/h005_information_ideas`, read-only, no numerical
trials, edits or children. Independent initial brief; no other H005 proposals.
Root records the substantive card below. Native Astra `/root/encoding_review`
has a separate read-only mathematical preflight. No verified improvement.

## Exact candidate

Let G generate an odd prime-order subgroup q of an ordinary E(F_p); Q=kG.
Let H=[2^(-1) mod q]G. For z in F_p use the lattice
L_z={(u,v) in Z^2 : u-zv=0 mod p}. Set h(z) to the squared Euclidean length
of a shortest nonzero vector, computed by exact two-dimensional lattice reduction.
For R != O define s(R)=(h(x(R)), int(x(R)), int(y(R))) lexicographically;
O has a unique smaller score. Representatives are in [0,p-1]. This is a concrete
readable score, not an assumed scalar predicate.

At R compute U=[2^(-1)]R and V=U-H; F(R) is the smaller-scored candidate.
Start at Q+rG for uniformly sampled known r. Track R_t=a_t Q+b_t G, with
(a,b) updated to (inv2*a, inv2*(b-d)), where d=0 selects U and d=1 selects V.
A collision R_i=R_j gives k=(b_j-b_i)/(a_i-a_j), provided the denominator
is nonzero, followed by explicit point verification. Use a cycle detector;
charge its extra function evaluations and all failed restarts. No secret-range
restriction or inverse table is supplied.

The speculative gain is a reduction of useful trajectory length, not that each
chosen digit is scalar parity. If a capped T=q^alpha trajectory gives a useful
collision with probability sigma, the proposed expected scale is
(T/sigma)*(C_half+C_score+C_tracking/detection), plus initialization and verification.
Direct subgroup halving costs O(log q) group operations, not a free half-step;
there are lattice scores and field/point costs. Fast binary-field prices do not
transfer. A claimed exponent improvement needs alpha<1/2, adequate sigma and
paid steps/setup. None is supported. Constant-memory cycle detection is possible.

## Proposed structural checks (under independent review)

Only 2R and 2R+G can precede R. The proposer derives
indegree(R)=1[s(R)<s(R-H)]+1[s(R)<s(R+H)].
Hence indegree is at most2 and the collision mass after one step from uniform
input is at most2/q. One-step concentration offers only a constant factor;
any exponent benefit would require an actual multistep phenomenon.
Since a_t=2^(-t), a same-trajectory repeat separated by ell has a zero recovery
denominator precisely when ord_q(2) divides ell. Such repeats are failures.
These are mathematical proposals, not Lean-certified or accepted based on agent
agreement. Inspect useful cycles, preimage multiplicities and O's basin; score
decrease or short useless cycles is not evidence of a solver improvement.

Rational reconstruction measures individual coordinate simplicity, but pointwise
reconstructions need not arise from one coherent rational lift. The doubling
formula alone implies no height descent. Modular reduction and arbitrary curve
coefficients are strong objections. No proven structural reason for gain exists.

## Primary-art screen

Inverse exponentiation with collision bookkeeping is already in Gadiyar–Maini–
Padma–Romsy, *What is the inverse of repeated square and multiply algorithm?*,
Colloquium Mathematicum116(2009), DOI10.4064/cm116-1-1:
https://www.impan.pl/shop/en/publication/transaction/download/product/87270
Its elliptic-curve note is specifically framed over binary fields; its existence
does not supply cheap prime-field halving or this score's performance. The inverse
walk wrapper is known. Originality of this particular score is unestablished.

Cheon–Hong–Kim, *Speeding Up the Pollard Rho Method*, ASIACRYPT2008:
https://www.iacr.org/archive/asiacrypt2008/53500477/53500477.pdf
is relevant primary comparison for iteration-cost improvements. Lower step cost
and shorter useful trajectories are separate claims. Root opened both primary
PDFs; neither validates this steering rule.

## Cheapest proposed falsifier and limitations

First check the exact map, recovery condition and score cost on paper. Only if
retained, freeze a tiny global-budget full-domain synthetic diagnostic comparing
useful collisions with matched rho and an independently random score under the
same wrapper. Count initialization, actual halving, scores, detection, failures,
verification and memory. A full-domain oracle/random-score table may serve as an
offline control only; it must not be free solver advice or a free runtime baseline.
No protocol, seeds or numeric results yet, and no unbounded score search follows.
Finite failure would reject this concrete steering rule operationally, not all
coordinate orderings; finite success would still not prove an exponent.

Other screened suggestions did not yield distinct concrete cards: power-residue
execution transcripts lacked a useful paid combination; coordinate-guided
Euclidean pair reduction lacked a coherent height; local minima were not global
orbit labels; learned translation eigenfunctions duplicated missing-feature and
generalization assumptions. These are not four additional mechanisms or universal
impossibility results. One concrete low-priority card is preferable to padding.
