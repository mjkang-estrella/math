# CM275 contribution review

Verdict **SUBSTANTIAL** on the complete frozen scope; no required contribution
or eligibility repair. Read review.md for the operation-level assessment and
read-limits.md for its actual bounds. This is not the separate full proof
gate or an acceptance/publication action.

From this directory, with Python 3 standard library:

    python verify.py --anchor EXTERNALLY_SUPPLIED_REVIEW_MANIFEST_SHA256

For exact replay against the sealed author packet:

    python verify.py --anchor EXTERNALLY_SUPPLIED_REVIEW_MANIFEST_SHA256 --author-root ../fresh-analytic-discovery-r26

The anchor is the SHA256 of output-manifest.json, supplied independently in
the reviewer handoff. An editable local hash is not a substitute. The verifier
authenticates before parsing payload metadata and performs no writes, network
requests or mathematical program execution. It rejects wrong anchors, changed
bytes, altered membership, symlinks and unsafe paths. It checks only recorded
byte identities; a positive return is not a mathematical or novelty proof.

The optional author path makes the review portable: review-only authentication
does not require the original workspace, while author authentication requires
the separate exact 69-file author packet. Original project-owned scope,
candidate and metadata snapshots are retained under inputs/; third-party
bodies remain privately in the author packet. No PDF typesetting QA was
required or performed for this contribution review.

The verifier's defensive path/JSON pattern adapts the inspected author
verify.py under its MIT license; the review-specific checks are original.
reproduction.json records pre-final-seal controls, followed by the final
externally reported positive replay. Adding that control receipt changes
the final review anchor; the chronology is explicit.

Author of original review prose/code: Myeongjin Kang, no affiliation.
Original prose CC BY 4.0, original code MIT; see LICENSES.md. The external
primary references and stipulated source retain their own rights.
