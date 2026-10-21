# Arithmetic136 / T054L136 — first correctness review

**Verdict: NEEDS_REPAIR for the entire unchanged frozen statement and author proof.**

Author proof §3, line 99, has a sign error: at p dividing a+1 the norm equation reduces to −x²=n, not x²=n. Frozen alternative (ii) therefore fails to supply the claimed obstruction when p≡3 mod4. This leaves the all-complements minimum bound, and thus the irrationality proof at lines 140 and 146, unproved.

The review proves an exact counterexample to the unconditional lattice lemma: B=4, a=18961 satisfies the frozen hypotheses, while <4> perpendicular <-359538482> is in the genus of N_a and occurs as a K3 Neron–Severi complement with the same integral transcendental Hodge lattice. This does not disprove the frozen theorem with its unknown B0. The supplied P1 is explicitly addressed, including the separate 3-adic exclusion for n=3m² and its failure to cure n=2.

[Complete mathematical review](notes/review.md) contains the derivations, conditional Source054 applicability checks, every-center and finite-order arguments, cubic/K3 and locus interfaces, exact arithmetic construction, and all frozen quantifier dispositions. [Reading and isolation record](private/READING.md) gives actual proof extents and limitations. All operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true; upstream truth was not audited.

The packet was independently selected and sealed once. Its private source/primary/history bodies remain local. No author input was edited, no sibling review was read, and no contribution, acceptance, priority, or counting determination is made. Read-only verification is provided by verify_packet.py; detached FINAL/MANIFEST/REPORT SHA256 anchors accompany the handoff.
