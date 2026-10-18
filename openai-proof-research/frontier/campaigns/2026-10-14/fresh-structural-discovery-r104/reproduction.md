# Reproduction and limits

Run the read-only verifier with the externally supplied MANIFEST.json SHA256:

    python verify.py --anchor EXTERNAL_SHA256 --repo /path/to/openai-proof-research

Its default private root is this packet's ignored private directory in that repository. An explicit --private-root allows an isolated copied private tree. The verifier authenticates exact PUBLIC membership, all payload bytes, the unchanged full scope, the complete13223-entry tree and immutable pin,19 canonical source Git blobs/SHA256 values, and three primary PDF/text pairs. No source or primary body is public. Private bodies are checked by receipt rather than included in public membership.

The two diagnostic scripts require Python with NumPy. They only write JSON to standard output:

    python coarse-diagnostics.py
    python volume-normalization-diagnostics.py

The recorded runs used /var/tmp/r99-eval-env/bin/python with its existing cached NumPy; no packages were installed. Floating diagnostics cover k=2,3,4 and amplified d=1,2,3. They check finite coefficient identities, dimensions, orthogonality, metric multiplicities and exact logarithmic exponent cancellation. They do not prove free probability, convergence of matrix volumes, or existence of entropy gaps. No full upstream compiler replay was performed or needed to stipulate source truths.

Copied verifier controls are recorded externally under /var/tmp/r104-final-controls.json after sealing: positive; wrong external anchor; altered candidate; missing candidate; extra public file; altered complete tree; altered canonical source body; altered primary PDF. Expected reasons are checked, not just nonzero exit codes. The copied controls do not mutate this packet or its private inputs.

The packet includes historical exploratory notes with their original uncertainty statements. candidate.md, its cited detailed proof notes, comparison.md and stress-checks.md specify the final author proposal. Earlier hidden-X concerns were corrected explicitly; no general upper Fisher continuity is asserted. Separate full-scope proof and contribution review are required. No formalization, manuscript, upload, acceptance or count change has occurred.
