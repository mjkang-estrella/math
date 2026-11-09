# CHECKPOINT — crown-vnumber-formal-pi-r7 (2026-11-06)

## Done

1. Bootstrap executed FIRST (exact command), receipt `bootstrap-receipt.json`
   preserved; affinity [0,1], CPU 10s/AS512MiB self-caps inside bootstrap.
2. TASK.txt read in full (15704 chars, bootstrap read).
3. Frozen verification BEFORE math reads: 484/484 sha256 match, 0 missing
   (verified with python3 -I -B inline; no writes outside lane).
4. Seven src modules copied from completed r6 only; hashes match root
   integration r6 exactly (all seven).
5. runner.py/check.sh: root-prepared copies with CPU120/AS12GiB own-caps,
   DEVGUARD 130 wired, outer 140. Validation pending -> see below.

## Runner validation (mandatory before real builds)

- [x] success path: `runner.py selftest_true -- true` exit 0, receipt kept
- [x] failure path: `runner.py selftest_false -- false` exit 1, receipt kept
- [x] baseline rebuild of the seven copied modules (fresh oleans in THIS lane)

## Mathematics (classification plan, locked)

Reduction: `VCut s t (t ∉ s) ↔ ∃ b c, b∈s ∧ c∈s ∧ cadj t b ∧ cadj t c ∧ ¬SameC s b c`
(neighbors of t in two distinct s-components). Forward: `sameC_ins_split`
gives H-paths x–t, y–t; a head-peeling path lemma extracts an s-path from x to a
t-neighbor; the two neighbors are then in different s-components, else x~y in s.
Backward: one-edge detour. With t = a_p the witnesses are forced Y-side.

Converse (cutset ⇒ shape), T ≠ ∅, D_X/D_Y = deleted index sets, C/D survivors:
- T ⊆ X: p ∈ D_X gives ∃ d≠e, ¬SameC s b_d b_e; the 2-hop (via a_c, c∈C, c∉{d,e})
  and 4-hop (C={d,e}, via b_f, f∉{d,e}, n≥3) force |C|≤1 ⇒ T=Xside or Xside∖{a_i}.
  (cx=2 excluded: all neighbor pairs 2/4-hop connected ⇒ no VCut, contradicting cutset.)
- T ⊆ Y: symmetric.
- both sides: p∈D_X ⇒ |C|≤2 and C⊆{d,e}⊆D; q∈D_Y ⇒ |D|≤2; distinctness ⇒ |C|=|D|=2
  and C=D ⇒ T = univ ∖ mixKeep i j, i≠j.

Each family is a cutset: explicit 2-edge witnesses; refutations via
no-edge-from-x lemma (side-independent sets) or a 2-tag coloring on the 4
surviving mixed vertices. Y-side families via the vswap transfer
(sameC_vswap / sameC_vswap_inv) or direct copy.

## Next (unpaid, in order)

FamPrime primality/distinctness and J = ∩ (separator route), then degrees 0..3
exclusion, quartic witnesses, VIs endpoint, audit/checker/replay.

## Honesty notes

- No endpoint, no classification theorem exists yet in this lane at checkpoint time.
- All exits/hashes reported come from actual receipts in `receipt/`.
