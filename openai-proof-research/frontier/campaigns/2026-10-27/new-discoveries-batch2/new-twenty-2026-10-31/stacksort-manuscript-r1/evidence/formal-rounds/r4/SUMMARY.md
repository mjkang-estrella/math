# Round 4 implementation: partial, not acceptance

Neither CommonCutCount nor MaximumFinalCount is closed in this packet. AdditiveRecursion, ExactSeeds20, Lower130 and the four source-reading endpoints therefore remain conditional. No self-acceptance or credit is claimed. Root decides.

New sorry-free proof content:

- StackSortCut4: a boundary determines its tuple prefix/suffix uniquely for tuples of nonempty words; existence of the last proper common cut; collision splitting; irreducibility of the final block; uniqueness of the entire prefix/final-block decomposition; a FinalBlock data structure with existence and subsingleton proofs; and the characterization of irreducibility by an empty remainder.
- StackSortLabels4: the literal sections enumerator commutes with every relabelling, including surjectivity; arbitrary labelled tuples are precisely the increasing images of literal standardized tuples; prescribed-label collision and irreducible families have exactly the unrestricted XI and II cardinalities.
- StackSortMaximum4: a maximum at the final output position lies in the tuple's last word; T2 specializes this to both literal tuples of an irreducible collision.
- StackSortDeletion4: deletion in an arbitrary tuple prefix, with the empty children omitted; exact arity shift; preservation and reflection of output collisions after deleting the terminal maximum.
- StackSortCount4: II(M,1,s)=XI(M,1,s), and the exact CommonCutCount equation when r=1.

StackSortFinal4 re-exports the source-reading endpoints with exactly CommonCutCount and MaximumFinalCount as explicit arguments, and the unconditional maximum-fibre endpoints. It prints the axioms of each endpoint. These conditional re-exports do not discharge the round-4 targets.

All 66 inherited source modules are preserved byte for byte. Their before/after hashes and the frozen archive hash are in hashes/. New modules are named StackSort*4*.lean. See results.json for final validation status, PROOF.md for the remaining constructions, and REPRODUCE.md for resource-bounded replay.

No child agents, git, network, browser tabs, shared ledger edits, external messages, publication or upload were used. All writes, temporary files, builds and caches are lane-local. The resource wrapper caps every Lean, leanchecker and Python process at two CPUs, 120 CPU seconds, 140 wall seconds and 6 GiB aggregate RSS, with MALLOC_ARENA_MAX=2 and -M3500 for Lean. No background job is retained at handback.

Final validation: all 73 modules passed a strict serial rebuild from the fresh extraction and explicit-module leanchecker. The audited set equals the final import closure: 349,298 declarations, including 842 local declarations, of which 125 are new in round 4. All local metadata flags are zero, and every audited new endpoint/helper dependency uses only propext, Classical.choice and Quot.sound. Peak recorded per-command RSS was 2,935,304 KiB; no RSS-watchdog kill occurred. The source archive SHA-256 is 46c01f2044c67acc490c8a48f0c7a860f89ea8299233368ca81e83f93765b0da. See results.json and fresh-extraction/logs/ for the complete records.
