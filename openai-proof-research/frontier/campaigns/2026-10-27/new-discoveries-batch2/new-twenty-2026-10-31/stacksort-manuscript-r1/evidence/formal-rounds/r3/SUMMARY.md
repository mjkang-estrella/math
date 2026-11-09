# Round 3 implementation — partial, not acceptance

RootSplit and DoublingInjection are now proved unconditionally. So is Doubling.
The source endpoints are NOT unconditional: AdditiveRecursion remains open.
No acceptance or credit is claimed; root decides.

All 57 inherited modules were merged without conflicts, with the 11 shared round-1 names byte-identical. All three input archive hashes match the brief. Every inherited module passed a strict serial rebuild before new module compilation. Before/after inherited hashes are retained.

Nine new modules provide finite-set increasing relabelling and its exact permutation-word image; preservation and reflection of collisions; choose-weighted word-pair shuffles; a general tuple-family tensor count, including prescribed labels and preservation/reflection of boundaries and irreducibility; the full root-split injection with all four end families; and unconditional doubling. StackSortFinal3.lean reduces the source endpoints to exactly StackSort.Seeds2.AdditiveRecursion, using the merged seed certificate and lower130 linkage.

The shuffle tensor count does not itself prove the unique common-cut decomposition or the counted maximum deletion identities. CommonCutCount and MaximumFinalCount in StackSortSeeds3.lean isolate those two exact natural-number identities; their conjunction is equivalent to AdditiveRecursion. Neither is asserted as a theorem without hypotheses. ExactSeeds20, Lower130 and the source refutation remain conditional on that proposition. The maximum-fibre refutation remains unconditional.

Validation status and evidence are recorded in results.json. See PROOF.md and REPRODUCE.md. No child agents, git, network, browser tabs, external messages, publication, uploads or shared-ledger edits were used. All writes, builds, temporary directories and caches are lane-local. No background job is retained at handback.

Completed validation: all 66 modules passed strict serial compilation from a fresh source extraction and explicit-module leanchecker. The audited set equals the endpoint import closure: 349,173 declarations from 3,583 modules, including 717 local declarations (90 new in round 3). Local unsafe, partial, _unsafe_rec, implemented_by, extern and axiom flags are all zero. All audited endpoint dependencies use only propext, Classical.choice and Quot.sound; upstream metadata is reported separately. The independent Python diagnostic checks literal P through 7, 136,673 root images through six non-root labels, and tuple collision/boundary/irreducibility invariance through size 4. This diagnostic is not used as a proof.
