# H007 complete-cost screen: no new survivor

Native Sol /root/h007_fullcost_schedules completed the explicitly recorded
reassignment after Factory Opus returned Internal error: Agent error without a
report. Read-only, no edits/experiments/numerical scratch. These are Sol findings,
not a successful Factory run. Root disposition: no experiment authorized.

1. Fingerprint-only signed BSGS: retain (keyed-universal-hash(x), baby index),
   including all duplicates. Reconstruct candidate scalars and verify kG=Q for
   every match, handling infinity separately. For m babies, g expected giant
   queries under a frozen comparator, t bits and verification cost V, expected
   false matches are bounded by roughly mg/2^t under the hash assumptions.
   Pay seeds+m*C_b+g*C_g+hashing+joins+(1+mg/2^t)*V+exceptions. Memory includes
   m*(t+ceil(log2(m))+record overhead), load factor/sort workspace and point buffers.
   A smaller record can improve a memory-constrained implementation, but the
   comparator must also receive this known-style compression. No novelty or
   superiority to compressed BSGS/optimized rho established. No actual memory
   cap or surviving full-cost inequality supplied; no separate research test.

2. Projective rho blocks with delayed normalization: next increments must depend
   invariantly on the group point for coalescence. Raw projective coordinates
   do not provide that property. Boundary-only normalization leaves an unspecified
   invariant partition or a changed walk needing mixing analysis. Fixed identical
   increments make a block a translation. Complete cost includes every invariant
   partition operation, projective addition, starts, endpoints, cycles and recovery.
   Reject as incomplete until an explicit cheaper invariant partition is given.
   This does not exclude all projective walks.

3. Endpoint-only scalar labels: retain seed and trail length, then replay colliding
   trails with labels to recover/verify. Search can omit routine scalar updates,
   but replay costs actual selected trail lengths; not automatically2/theta, since
   selection biases lengths. Transport signs/endomorphisms must replay identically;
   all failed/capped trails, seeds and endpoint storage remain paid. Overlaps H002
   reconstruction/lazy-label cards and established distinguished-point recovery.
   No distinct new mechanism; do not reopen from relabeling alone. Even free labels
   save at most their measured share of the matched solver's total cost.

Sources inspected by proposer:
- Galbraith-Wang-Zhang paired BSGS and inversion baseline:
  https://www.aimsciences.org/article/doi/10.3934/amc.2017038?viewType=HTML
- EFD coordinate relations: https://hyperelliptic.org/EFD/g1p/auto-shortw.html
- van Oorschot-Wiener sections4.1-5.1:
  https://www.scs.carleton.ca/~paulv/papers/JoC97.pdf
Two direct ePrint PDF fetches failed, not treated as inspected full texts.

No predicted exponent change, benchmark or accepted whole-solver gain. A future
fingerprint implementation comparison first needs a concrete finite memory cap
and inequality beating a baseline allowed identical compression. It would remain
an implementation comparison, not a novel ECDLP complexity result. Best supported
classical reference remains square root; verified improvement NONE.
