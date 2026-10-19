# Identity validation, not mathematical gates

The author six handoff anchors matched before reading and after completion. All65 author-root files have identical before/after byte lengths, SHA256s, modes and hardlink counts in the private snapshots. Their snapshot digests are identical in `immutable-input-check.json`. The independently replayed author verifier accepted its exact62-payload packet, FINAL/freeze bindings,19 canonical source blobs and four primary PDF/text pairs at the handoff identities. The review's separate verifier independently repeats those checks without executing author code.

The author control code was read before execution, copied to a disposable author-root copy under this assigned directory, and run there with the supplied manifest and FINAL anchors. All22 cases passed. `author-controls.json` is the actual unchanged receipt produced on that copy; its phrase “original packet” refers to that copied baseline. The separate whole-author snapshots establish preservation of the immutable source originals. No deliberate mutation was ever made in the real author root.

Expected author rejection reasons, compared with the actual receipt:

* Wrong manifest argument: FINAL-to-manifest binding rejection; missing manifest/FINAL anchor: argparse requires the absent argument; wrong FINAL anchor: detached FINAL mismatch.
* Changed report, proof, frozen target, source blob, primary PDF or verifier payload: named file metadata/hash mismatch.
* Missing/extra file or extra directory: exact membership/directory metadata mismatch.
* Symlink: symlink rejection; hardlink: nonregular/hard-linked rejection; file mode: metadata/hash mismatch; packet root mode: root/manifest mode mismatch.
* Changed manifest or report resealed only with a new manifest: detached manifest mismatch. Changed FINAL metadata or report+manifest+FINAL resealed together: detached FINAL mismatch.

The baseline was expected to accept. Each of the21 negative cases rejected for its expected reason, with the copied baseline and verifier-input snapshot unchanged during each invocation.

This review's own `controls.py` tests28 additional cases: one copied positive baseline and27 meaningful failures, including wrong/missing detached review anchor, altered review/reading limits/verifier/private PDF, file/directory membership, symlinks, hardlinks, modes, self-resealing, changed author anchor bindings, each of the six author anchors, changed author source/primary, and changed complete-tree bytes. Each case records an explicit expected rejection substring, actual exit status and output, and before/after equality for all verifier inputs. It invokes the trusted original review verifier on COPIES, so a modified verifier payload cannot certify itself.

All28 cases passed before final sealing. A final replay with `--check-record` is required to match this same receipt byte for byte after sealing. The verifier prints no self-referential manifest digest into the receipt; the external review-manifest SHA256 is supplied in the final handoff. This avoids a circular seal. Its successful replay authenticates the receipt without rewriting it. Final direct verification of the original sealed review is also read-only.

There are50 copied integrity scenarios in total, with48 expected rejections and two positive baselines. They are byte-identity controls, not50 mathematical checks. No finite mathematical calculation is claimed to establish the general density, boundary, source or contribution assertions. The verdict in review.md is a separate reasoned contribution judgement conditional on correctness.
