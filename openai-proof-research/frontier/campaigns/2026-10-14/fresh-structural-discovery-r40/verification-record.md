# Verification record and replay

The substantive result is UNRESOLVED/no nominee. All checks below are author-side diagnostics or provenance checks, not an independent review, Lean verification, or proof of the target.

Run the read-only verifier with the MANIFEST.json SHA256 obtained independently from the parent handoff:

    python -B verify.py --expected-manifest-sha256 <external-anchor>

Do not derive the expected anchor from the packet as the trust source. The verifier checks the exact file and directory inventories, every payload size/hash, the frozen scope hash, all32 pinned Git blob identities against the saved complete-tree selection, and all4 primary PDF/text identity pairs. It rejects root/payload symlinks, hardlinked regular files, nonregular nodes, nested manifests, extra files, and extra empty directories. It writes nothing. It does not contact the network, audit source mathematics, or reread external mutable campaign notes.

checks/diagnostics.py uses exact dynamic programming for36 explicit rotation pairs, checks1,008 interior grid-offset blocks, and checks124 exact rational binomial one-step TV identities. Eight exact rational trace-distribution comparisons are recorded; for K2/3 and N10/20/40/80 they decrease as predicted. These finite data do not prove the asymptotic estimate; failed-repairs.md supplies that argument.

checks/integrity-controls.json records12 copied-packet controls: positive copy; wrong external anchor; payload change/deletion; extra file/directory; root/payload symlinks; hardlink; FIFO; nested manifest; and mutation plus self-resealing against the old external anchor. Every result matched its expected accept/reject status. The control run used the intermediate complete packet before adding its JSON result and this verification record; these additions are covered by the final manifest. Final caller-anchor positive and wrong-anchor checks are run after that final manifest is made, with results reported externally to the parent.

One initial harness attempt redirected stdout to a new in-packet result file after its intermediate manifest was made. The positive-copy test correctly rejected the extra file. The empty output was removed, the manifest regenerated, and stdout captured in memory before writing the completed result. No verifier check was weakened. Temporary copies lived only under owned checks/control-work and were removed before the seal.

To replay diagnostic code without modifying a sealed packet, print its output to the caller's console. A copied-control replay needs a disposable copy with scratch below its checks directory; do not write result output into the sealed packet while controls are running. No randomized seed is needed: the finite test domains are exhaustive as stated, and all probability distributions in these checks are enumerated exactly.

The original-scope hash was checked unchanged before seal. Private bodies are excluded by this packet's .gitignore. No files were staged or committed. The external manifest hash is delivered to the parent outside the packet to avoid self-anchoring.
