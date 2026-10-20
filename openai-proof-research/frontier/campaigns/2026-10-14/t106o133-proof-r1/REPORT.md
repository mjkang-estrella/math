# T106O133 independent correctness review r1: PASS (full frozen scope)

Reviewer: Factory Droid / claude-opus-5-5. Date 2026-10-20. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(stipulated true including operative proof operations; upstream truth not audited). This is the first
independent correctness verdict for T106O133. It makes no contribution, acceptance, count, novelty or
priority judgment.

**Verdict: PASS** for the unchanged frozen scope (author frozen-statement SHA256
`72654d283495baa80aba6349b1b5ebb9a4634ba268d7499a6187ecdd1e311256`):

- Theorem A for every fixed integer k >= 1 and every fixed real delta > 0.
- Corollary B for all finite loopless H, G with H non-bipartite and H -> G. This covers the decision
  problem PCSP(H, G) and the promised search problem under polynomial-time Turing reductions.
- The density form.

No blocking gap was found. Full reasoning is in [review.md](packet/public/review.md). Read limits are in
[reading-limits.md](packet/public/reading-limits.md) and rights in [rights.md](packet/public/rights.md).

**What was verified against my own pinned copies of source 106.** I read all eight section files and
main.tex line by line. Their git blob SHA-1 values match the complete 13223-entry tree.

- Every fixed threshold in the source occurs only at eq:clique-test, eq:edge, the prop:encoding
  comparison, lem:completeness, eq:independent-separation, eq:bumps, and "L = 64" in lists,
  coefficient and parameters. The author replaced each of these.
- All later steps use only the following facts: f is odd, takes values in [-1,1], equals 1 on A, is
  constant across zero links, and is L-Lipschitz within copies. Apart from these facts, they use only
  the symbol L. thm:junta and lem:influences hold for every finite L.
- With rho = 1/(4k+2), each of these properties holds for the bump (1 - u/rho)_+ with
  L = 8k+4. f = 1 on A uses the strict separation dist(A,TA) > rho.
- The parameter order can be rerun with L = 8k+4, and no constant depends on the Label Cover alphabets.
- The new completeness colouring is endpoint-safe for every k >= 1: arcs [j/N, (j+1)/N) with
  N = 2k+1, index differences k or k+1, and the map j -> -2j into C_N.
- In Corollary B, the odd cycle, the fibre counting for loopless G and the search-to-decision
  check are correct.

Non-blocking remarks are in review.md Section 7. R1: for large delta, the density promise sets can
overlap; the many-one reduction is still what is claimed, and delta_0 <= 1/|V(H)| avoids the overlap.

**Requested comparison points.** The proof does not use any 2-to-1, Rich 2-to-1 or FMW input. Pinned
106 (intro lines 106-112) and pinned 105 (intro lines 75-81) both state that the Rich condition is not
part of 105's ordinary 2-to-1 theorem. The FMW supplement was not located or read.

**Evidence and limits.** I authenticated the five author anchors. I fingerprinted all 56 author files
before reading and again before sealing; nothing changed. Contribution briefs, contribution results,
in-progress roots, arithmeticr97 and analyticr131 were not read. There was no web search, large
computation, nested agent, git or shared-index change, upload, contact, browser UI, formal work or
manuscript work. The only computation was a small exact-rational arc control
(`arc_check.py`, k = 1..7) with a negative control. It is not a proof.

Packet MANIFEST SHA256: `9939e7ab60fd1a004d9f20c7ec74a75a86473d5f83573ad175fed311e02b65ca`.
Review SHA256: `991e748640f3003ff044e9f3f395558b52b14bb3864f202f3dd58843139e22bb`.

FINAL.json binds this report, the MANIFEST, review.md, input-fingerprints.json and the explicit author
anchors. Supply its SHA256 DETACHED from the handoff. The verifier is read-only:

    python -B packet/public/verify.py --root . --project /home/mj-kang/Documents/Dev/math/openai-proof-research --finalhash DETACHED_SHA256

The copied controls run only on temporary copies under `controls/`. They write the receipt
`controls/artifact-controls.json`, which is outside the packet and not bound by FINAL:

    python -B packet/public/controls.py --root . --project /home/mj-kang/Documents/Dev/math/openai-proof-research --finalhash DETACHED_SHA256

Artifact checks are not mathematical gates.
