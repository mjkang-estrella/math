# I308 — reading record and failures

2026-10-13. Work confined to `/home/mj-kang/Documents/Dev/math/openai-proof-research`. Only the five assigned I308 files were written. No subagent, live Gaussian review I303/I304, live future contribution review, git operation, publication, numerical scan, or shared-index edit was used.

## Actual semantic reads

- `AGENTS.md` lines 1–11 and `sources/upstream.json` lines 1–6: scope, stipulation, immutable revision, write restrictions.
- `frontier/iterations/i307-disk-extremizer-spectrum.md` lines 1–101: complete target, including theorem, every proof step, nilpotent supremum, R019 consequence, and stated novelty limits. Read fully and reread with line numbers; requested SHA256 matches.
- `frontier/experiments/i307_disk_extremizer_spectrum/input-authentication.json` lines 1–55: complete supplied authentication. Every whole-file record and every passage record checked.
- `frontier/sources/i287_crouzeix_repeated_support/direct-pinned-main.tex` lines 30–95 and 286–455: actual `thm:main`, original-resolvent positivity, `thm:domain`, the bilinear functional, ordered products, weighted dual tests, diagonal/cross Parseval, and positive block comparison through the completed inequality. This is the existing authenticated pinned body, not a new retrieval. The upstream theorem is stipulated; all new disk deductions are independent.
- `frontier/iterations/i306-strict-scalar-complete-gap.md` lines 1–80: complete earlier proposal, to identify G306, its power data, and its different ACV-dependent route. That external route is not used in this review's proof.
- `frontier/findings/R019-entangled-complete-crouzeix-equality.md` lines 1–87: accepted exact N/P construction and scope boundaries.
- `frontier/experiments/i287_crouzeix_repeated_support/analysis.md` lines 1–288: original construction/proof, including exact norms at lines 266–288; those last lines were reread with line numbers. No history replay occurred.
- `frontier/reviews/i291-crouzeix-counterexample-proof.md` lines 1–17: completed review, used as provenance corroboration. New deductions and the relevant exact norms were independently checked, not inferred from its verdict.
- `frontier/experiments/i287_crouzeix_repeated_support/input-authentication.json` lines 250–304: existing pinned-source URL/hash provenance; an earlier lexical search also located its source entries. No unrelated input bodies referenced there were opened.
- `frontier/sources/i287_crouzeix_repeated_support/literature.md` lines 1–12: existing source URL/hash normalization and source-method attribution. A lexical search located the pinned direct URL; its structural-companion reference was not a proof dependency.
- `sources/CONTENTS.md` semantically lines 7924–7949: family 325 and the two manuscript catalogue entries. The actual direct theorem was read separately; catalogue summaries were not theorem premises.

All whole-file and semantic passage hashes for these inputs are in `input-authentication.json`. A full-file hash verifies identity, not a claim of full semantic reading unless expressly listed above. Raw source URLs in the literature file are provenance URLs for existing authenticated material. No external source was newly fetched or retained.

## Operational issues and corrections

An initial file-inventory search returned many unrelated archived AGENTS/upstream filenames. It did not open their bodies. A later instruction search listed nested AGENTS filenames; none governed the assigned output paths. The repository-root AGENTS applies.

An overbroad `cat sources/CONTENTS.md` in a batched read produced a truncated catalogue output and made the combined response unwieldy. No full-catalogue semantic reading is claimed. This was corrected by bounded family-325 reads and by rereading the complete direct proof/target material separately. It was a catalogue output mistake, not a mathematical failure or a history replay.

The first passage-hash trial used original bytes with terminal newlines and therefore did not match the parent's passage values, while every whole-file hash matched. A second trial used UTF-8 `"\n".join(splitlines()[start-1:end])` with no terminal newline. All four supplied passage hashes then matched exactly. This resolves a hash convention, not an input change. Both the raw-file convention and the passage convention are explicit in the new authentication record.

No mathematical failure or counterexample was found. No external retrieval failed, because none was necessary: the direct pinned source was already available and ACV/Crabb/Berger–Stampfli equality statements were not premises. The proof has no unpaid operation for this assigned target. The separate future contribution gate remains outside scope.

## Validation method

Hand-derived identities and exact radicals verify the generic coefficient/block argument, reversed minimal-polynomial degrees, compactness and approximation, and the three N power norms. Hash checks use SHA256 only. No numerical samples, floating-point norm optimization, or parameter sweep was performed. The authored proof review expands justification; no target repair or hidden hypothesis was introduced. Detached SHA256 values of all five outputs are returned after writing, avoiding a self-referential hash in this record.
