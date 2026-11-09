# Deleting the original associator density: exact leakage bookkeeping

Author continuation of the unchanged full T101G69 target. Assume B(T)=I in this note. Let D be the original positive associator-density matrix, tr D=C. Fix d0>0 and let Q=1_(d0,infinity)(D), P=I−Q, r=rank Q<=C/d0. Put S=P^tensor3 T on PV. The first deletion costs ||T−S||HS²<=3r by symmetry. None of the estimates below licenses an indefinite sequence of such deletions.

## 1. Compression associator and its two different scales

Let Z:QV->PV tensor PV have coefficients Z_(ij),q=T_ijq. Then Z*Z<=I_Q. Write Z_q=P X_q P and

  M=sum_q Z_q²,
  H=K(Q)=sum_s X_s Q X_s.

Full symmetry gives sum_q X_q²=K(Q), hence M<=P H P. Also tr M=||Z||HS²<=r and ||M||op<=1.

Restricting the original associator to all four P indices, the compression associator differs by two permuted contractions of Z*Z:

  A(S)(x,y,z)=P A(T)(x,y,z)
       −P mu(Q mu(x,y),z)+P mu(x,Q mu(y,z)).

The inherited one-versus-three operator norm is at most sqrt(2d0), because its singleton input lies in P and the original singleton Gram is2D. Each error has total HS norm <=||Z||op||Z||HS<=sqrt(r). Its singleton flattening is bounded by ||Z||op sqrt(||M||op). Therefore

  ||A(S)||HS<=||A(T)||HS+2sqrt(r),
  eta_1(A(S))<=sqrt(2d0)+2sqrt(||M||op),               (1)

where eta_1 denotes the largest singleton flattening norm. In contrast, its natural pair flattening can have norm1. Trace-paid rank does not make this error operator-small.

The compressed Gram has an exact positive loss decomposition. Define

  N_ij=sum_(q,q' in Q) T_iqq' T_jqq',
  F=I_P−B(S).

Then

  F=2M+N>=2M>=0,   F<=I_P,   tr F<=2r.               (2)

The trace bound follows by charging coefficients with at least one Q input to twice the one-mode Q energy r. Thus (1) also gives eta_1(A(S))<=sqrt(2d0)+sqrt(2||F||op). In particular both the new Gram error and the new singleton density would be small if F were operator-small. Its trace alone does not imply that condition.

## 2. A localized commutator estimate for the leakage operator

Use the exact F_rs,E_rs notation from channel-density.md. Define

  A_s=sum_r E_sr Q X_r.

Symmetry of T cancels the F_sr terms in the commutator expansion, giving

  [X_s,H]=A_s−A_s* .                                  (3)

The fixed column family (QX_r)_r has norm at most1, because sum_r X_r Q X_r=H<=I. Row Cauchy–Schwarz consequently gives

  sum_s A_s A_s* <=sum_sr E_sr E_sr*=2D.               (4)

The opposite Gram requires a different argument; it does not follow by transposing (4). The block operator E=(E_sr)_(s,r), acting on V tensor V, is S_channel−K up to the fixed ordering of indices. Indeed

  (E_sr)_ab=sum_t T_sat T_rbt−sum_t T_srt T_abt.

The first term is JJ* and the second is K under vectorization. Both have operator norm at most1 when B=I. Thus ||E||op<=2. Since the stacked column (A_s)_s is E applied to the stacked column (QX_r)_r,

  sum_s A_s* A_s<=4H.                                 (5)

Combining (3)–(5),

  sum_s [X_s,H]*[X_s,H] <=4D+8H.                      (6)

This gives an operator density bound on simultaneous low-D and low-H vectors. It is an exact inequality, not a commutation assertion between D and H. It does not give a gap for a spectral cutoff of H.

## 3. Why the next deletion is not yet paid globally

Deleting the eigenspace of M (or F) above a fixed threshold costs at most O(r) further directions. But this new projection changes the product again. The new contracted terms involve the newly deleted directions, not only the original Z. Bounding their traces by the new rank gives a multiplicative rank recurrence, which can grow over arbitrarily many steps. Equations(1),(2),(6) do not currently provide a decreasing potential that sums those losses.

Nor can a gap be inserted at a chosen eigenvalue threshold without proof. Low and high spectral vectors can lie arbitrarily close to that threshold. The high-K cutoff problem recorded in global-reduction-gap.md is a separate instance of the same need for an actual spectral-gap argument.

One possible replacement operation would complete the compressed Gram by adding new coordinates instead of deleting again. If one adds a new coordinate with old-old-new slice A, the old Gram gains2A². Taking A=sqrt(F/2) would repair the old-old Gram block. However it also creates cross Gram entries <S_i,A>, and the new diagonal Gram entry is tr(F)/2. These must simultaneously match an identity Gram. A general trace-paid symmetric completion satisfying those cross and new-block constraints has not been constructed. Simply inserting a square root is not a solution.

## 4. Status

This note gives exact first-step loss and localized commutator bounds. It neither proves a noncascading deletion theorem nor constructs the required global replacement. The original all-dimensional, all-error target remains unchanged and unresolved. The earlier exact-B/small-D supporting theorem is not used to bypass these missing hypotheses.
