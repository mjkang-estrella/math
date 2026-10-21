# Final bounded checks

Recomputed19 pinned source object sizes, Git blob SHA1 values and SHA256 values; total490431 bytes. Recomputed incoming and selected primary identities for all five versioned downloads. Compared the13 selected completed local-original copies byte-for-byte with their direct originals after copying. These checks establish selected-byte identity, not reading coverage or mathematical correctness.

Six copied-control invocations behaved as expected: baseline and restored baseline accepted; modified payload, missing payload, hidden extra payload and wrong detached anchor rejected. Verifier calls left copied file bytes unchanged. No source original was mutated. No standalone mathematical test or adversarial review was performed; the calculations remain prefreeze research notes and no correctness grade is assigned.

The root packet is sealed once after these checks. The root read-only verifier result and independently computed SHA256 anchors are returned outside the manifest in the parent-facing handoff; no post-seal file is appended. The three root envelopes are intentionally excluded from the manifest payload and checked by mandatory detached anchors.
