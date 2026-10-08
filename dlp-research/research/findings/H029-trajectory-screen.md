# H029 trajectory and endpoint proposals: initial disposition

2026-10-08. Native Astra initial time-memory/geometry role COMPLETED with no
surviving new card. Root checked the exact conjugacy identity and scopes below.
No numerical work, imports, code or Lean claims. Complete-work improvement NONE.

## Phase-dependent affine translations

For public invertible labelled translations T_r, maintain P=T_r(Z) and update
Pprime=T_(r+1)(F(T_r^{-1}(P))). Normalizing gives
T_(r+1)^{-1}(Pprime)=F(Z) exactly. Hence normalized collision events and label
recovery are those of the original walk. Maintaining Z simply uses that walk;
maintaining P adds transformations. This rejects the alleged EXTRA normalized
collision opportunities from this precise conjugation. It is not a lower bound
for every representation or a nonconjugate transition, nor does it claim raw
cross-phase equalities have the same detection semantics.

## Sparse macro endpoints and label replay

Two other attempted cards retain endpoints of F^L or remove stored affine
labels and reconstruct them by seed/trail replay. The former needs phase and
interior-collision detection rules already identified in H027; arbitrary block
endpoints do not automatically inherit all interior hits. A common distinguished
rule is established practice. The latter can replay at most2Lmax transitions
for two capped trails, with scalar setup, labels, null relations, restarts and
verification paid. No new cheaper record or recovery mechanism was supplied.

Primary baseline read by proposer: van Oorschot–Wiener,
[Parallel Collision Search with Cryptanalytic Applications](https://www.scs.carleton.ca/~paulv/papers/JoC97.pdf),
discussions of cycle detection, distinguished points and parallel walks. The
author-hosted copy succeeded after another host failed. Root's earlier accepted
baseline already credits seed replay; no novel algorithm is claimed from it.

Disposition: no new experiment admitted. Reopen with an actual nonconjugate
transition plus useful-hit/detection premise, or a concrete record layout that
beats the paid seed-replay comparator. This initial role's result does not reject
other H029 lenses. All failed cards retained without inflating an idea count.
