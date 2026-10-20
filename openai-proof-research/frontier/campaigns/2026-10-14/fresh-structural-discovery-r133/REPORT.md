# Structural r133: frozen author-proof nominee (family 106)

A full author proof is submitted for a statement frozen before proof drafting. No correctness, contribution, acceptance, count or priority verdict is assigned. Runner: provider Factory Droid, model claude-opus-5-5 (high). Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

Read the [public report](packet/public/report.md), the [frozen statement](packet/public/frozen-statement.md), the [author proof](packet/public/proof.md), the [working notes](packet/public/working-notes.md), [reading limits](packet/public/reading-limits.md) and [rights](packet/public/rights.md).

**Frozen nominee.** Theorem A: for every fixed k >= 1 and delta > 0, a deterministic polynomial-time reduction from 3SAT gives graphs that are C_{2k+1}-colourable (homomorphic to the odd cycle) when satisfiable and have independence ratio below delta when unsatisfiable. Corollary B: the Brakensiek-Guruswami conjecture (KOWZ Conjecture 1.2): PCSP(H, G) is NP-hard for all finite loopless H, G with H non-bipartite and H -> G. Frozen statement SHA256 `72654d283495baa80aba6349b1b5ebb9a4634ba268d7499a6187ecdd1e311256`.

**Mechanism.** The pinned 106 reduction (three-colourable vs independence ratio < delta) uses a half-shift edge threshold 1/8; its soundness uses the threshold only through a bump function with Lipschitz constant 64, after which every constant is chosen from that constant. Replacing 1/8 by 1/(4k+2) and 64 by 8k+4 keeps the soundness interface intact, while satisfying phase evaluations now place neighbours within 1/(4k+2) of antipodal, so 2k+1 arcs give a C_{2k+1}-colouring. The proof tabulates every later source step and the property it consumes.

**Strongest integrated reduction.** The 106 theorem as a black box covers only H containing a triangle; KOWZ (G = K_3) and Avvakumov et al. (4-colourable G) cover chi(G) <= 4. Odd girth(H) >= 5 with chi(G) >= 5 is left by these; KOWZ note that iterating their arc-graph reduction cannot get PCSP(C_5, K_c) from PCSP(K_3, K_c). Mechanically, the operation here is a threshold change inside the source proof plus a new completeness colouring; whether that is substantial or TECHNICAL is for the separate contribution review.

**Literature status found.** arXiv 2605.09815v2 (18 Oct 2026) describes the conjecture as following from the Rich 2-to-1 Conjecture and approximate graph homomorphism as unclassified. FMW (ECCC TR26-179 / arXiv 2610.12378v1) does not mention it; their supplementary material was not found or read. Project history shows no work on this mechanism. New to this project; no worldwide-priority claim. Search limits are in the reading-limits file.

**Disclosures.** A catalogue-title extraction was briefly written to /tmp at the start and moved into this root at once. Harness tooling may have stored command outputs outside the root; no other author writes occurred outside it. No nested agents, git or shared-index changes, browser UI, publication, upload, contact, formal, manuscript or release work occurred. Active rounds r97 and analytic r130 were not entered.

Packet MANIFEST SHA256: `a14d03fcc107582ad645e175e83ed765974805313e43e1958801088a6011cdaa`.
Public report SHA256: `f50a971b2aafa0d35004b2e118413e48e646790e42044285b61d783df084e969`.

FINAL.json binds this outside report, the packet manifest, the public report, the proof and the frozen statement. Supply its SHA256 DETACHED, from the parent handoff; FINAL.sha256 and REPORT.sha256 are convenience copies only. Verification is read-only:

    python -B packet/public/verify.py --root . --project /home/mj-kang/Documents/Dev/math/openai-proof-research --finalhash DETACHED_SHA256

Copied controls (run on copies inside this root; receipt `artifact-controls.json` is outside the packet and not bound by FINAL):

    python -B packet/public/controls.py --root . --project /home/mj-kang/Documents/Dev/math/openai-proof-research --finalhash DETACHED_SHA256

Artifact checks are not mathematical gates.
