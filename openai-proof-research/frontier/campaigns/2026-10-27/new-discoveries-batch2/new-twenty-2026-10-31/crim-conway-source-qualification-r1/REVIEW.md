# MathDB 375373 — source and ordinary-mathematics handback

Disposition: PARK. Accepted campaign count remains the user-supplied 52/60 beyond 39; lane credit 0. No full nonempty converse proof, certified nonempty counterexample, formal endpoint, acceptance, or execution recommendation. No dormant Pi brief is proposed because source/prior eligibility and a meaningful source-qualified test range remain open. This does not assert that a future bounded investigation is impossible.

## Separate gates

1. Literal scope: HOLD. literal-target.json/jsonl and target-provenance.json describe all partitions without an explicit nonempty restriction. The source includes the empty partition in Section 2.1; it defines CP(empty)=(0,1). Hooks are Gamma(r,c)=[c,1^(r-1)] for r,c>=1. Empty is not a hook. The unqualified biconditional therefore has the known terminal exception. This is a correction and never credit.
2. Intended scope: IDENTIFIED, fidelity adjudication HOLD. For every finite NONEMPTY partition lambda, CP_CRIM(lambda)=(0,1) iff lambda=Gamma(r,c) for even positive r,c. Both r,c are at least 2. These count all rows/columns, including the corner; they are not the arm/leg counts with the corner omitted. Restoring nonemptiness is an interpretation, not a silently altered MathDB endpoint.
3. Ordinary mathematics: HOLD. The hook implication is already Theorem 19. No full converse or substantive witness was obtained. Exact residual below.
4. Source/version: PARTIAL / HOLD. Current abstract and explicit v1 body retrieved; both match frozen bytes. Thesis body and 2022 predecessor not read. No blanket claim that all citing companions or corrections are cleared.
5. Prior/subsumption: HOLD. Current registries checked only to bounded routing depth. Known hook direction, empty correction, and mere formalization are excluded. No demonstrated reduction of the FULL nonempty converse to a public theorem was found, but missing source bodies cannot establish absence of such a reduction.
6. Novelty: HOLD. Open labels, empty solution arrays, and failed access do not establish worldwide novelty.
7. Significance: HOLD. A full intended converse or genuine nonempty counterexample could be substantive, subject to independent adjudication. Ease is not itself an exclusion; neither a known implication nor a parameter instance resolves this gate.
8. Pi recommendation: PARK / NO BRIEF / NO EXECUTION. No worker, diagnostic, Lean implementation, solver, enumeration, replay, or acceptance was run. There is no guarantee of formalizability or a new result.

## Exact game and termination

A partition is a finite weakly decreasing list of positive integers, with empty allowed for recursive evaluation. Row i removes exactly that part. Column j, 1<=j<=lambda_1, subtracts 1 from every part at least j and drops zeros. This follows from Section 3's definition as conjugation, row deletion in the conjugate, and conjugation back: in each original row precisely its square in column j disappears if present. Parts above/below the removed line reattach; this is not corner deletion, truncation, or LCTR. Sorting is preserved by the operation. Every legal move strictly lowers the sum of parts, so induction on area is well founded. Conjugation bijects the legal options, hence preserves both values by induction.

Write N(empty)=0, M(empty)=1. For NONTERMINAL lambda, N(lambda)=mex{N(mu):lambda->mu}, M(lambda)=mex{M(mu):lambda->mu}. CP=(N,M). M is the recursive misere Grundy invariant of Section 2.3; no disjunctive-sum theorem for misere play is assumed. Empty is the unique terminal partition because a nonempty list has a row deletion.

## Independently checked hook calculation (known, not new)

For a row [c], c>=1, options are empty and, if c>1, [c-1]. At c=1 CP=mex{(0,1)}=(1,0). For even c, its predecessor is (1,0), so mex{(0,1),(1,0)}=(2,2); for odd c>1, its predecessor is (2,2), so mex{(0,1),(2,2)}=(1,0). Conjugation handles columns. Theorem 17's printed 'nonnegative c' and its assertion about c=0 conflict with its own empty convention; only c>=1 is used here. This is another endpoint issue, not a result.

For H(r,c) with r,c>=2 the option set, allowing duplicate descriptions, is column(r-1), H(r-1,c), row(c-1), H(r,c-1). These are all possible row/column deletions. At H(2,2), options are [1] and [2], yielding mex{(1,0),(2,2)}=(0,1).

For r=2,c>2 the options can be written row(c), row(1), row(c-1), H(2,c-1). If c is even they have pairs (2,2),(1,0),(1,0),(3,3), giving (0,1). If c is odd they have (1,0),(1,0),(2,2),(0,1), giving (3,3). Conjugation gives c=2. For r,c>2 induction on r+c gives: both even, option pairs (1,0),(3,3),(1,0),(3,3), mex (0,1); both odd, pairs (2,2),(3,3),(2,2),(3,3), mex (0,0); opposite parities, pairs (1,0),(0,0),(2,2),(0,1) up to permutation, mex (3,3). Boundary cases must not be inferred from the interior table. This closes precisely the source's hook direction, not its converse.

## Sustained nonhook converse attempt and exact residual

Let O(lambda) be the full legal-option set. For N(lambda)=0, every option has N>0. For M(lambda)=1, at least one option has M=0 and no option has M=1. Thus the sought induction needs simultaneous information about sets of options with M=0 and M=1, not merely smaller (0,1) positions.

A precise sufficient AND necessary remaining statement, given the hook classification above, is:

(C) For every nonempty NONHOOK lambda with N(lambda)=0, if some mu in O(lambda) has M(mu)=0, then some nu in O(lambda) has M(nu)=1.

Indeed if no M=0 option exists, M(lambda)=0. If it does and (C) holds, mex is at least 2. Conversely a failure of (C), together with N(lambda)=0, is exactly a nonhook CP=(0,1) witness. The two options need not be the same partition, and no assertion N(mu)=1 is justified.

Attempt 1: assuming only all smaller (0,1) positions are hooks does not control M=1 children with N>0, or M=0 children with arbitrary positive N. A response yielding a normal P-position only proves its parent has N>0; it says nothing about its M-coordinate. This prevents both the one-coordinate induction and normal response-pairing arguments from closing (C).

Attempt 2: strengthen to simultaneous swap/domestic classification. This is not supplied by hook closure. Section 4 proves that the full game is not domestic and not returnable; it gives CP([4,3])=(0,4) and uses a nonhook [3,2,2,2,1] with CP=(1,0). These are source examples, not newly computed certificates. In particular, claiming all M=0 positions are rows, or all nonhooks are symmetric/tame, is incompatible with the source. We do not use a restricted hook game's returnability for full CRIM.

Attempt 3: split by geometric distance from hooks. A row deletion can produce a hook only if the original partition has at most two rows of length at least 2: after deleting one row at most one such row remains. Dually, a column deletion can produce a hook only if at most two columns have height at least 2. Consequently if lambda_3>=2 AND lambda_2>=3, no option is a hook. (The parts in this condition exist.) This proves a genuine structural barrier to a hook-option-only induction on the interior, but not (C): nonhook options can still have unequal coordinates. Near-boundary shapes and their descendants must also be controlled, so peeling back to hooks is not a closed simultaneous invariant.

An exact boundary recurrence illustrates the unclosed dependency without running a sweep. For a>=b>=2, options from [a,b] are rows [a],[b], the shape obtained by dropping zeros from [a-1,b-1], and [a-1,b] only when a>b. Componentwise mex applies. The hook boundary b=1 is known, but arbitrarily increasing b requires new off-diagonal boundary values, not just the classification of (0,1). No finite table, automated mathematical search, or asserted universal invariant was used. No example of a nonempty nonhook with CP=(0,1) is certified.

## Source, version, and chronology inventory

Frozen r322 relevant reads: literal 375373 record/provenance; ATTEMPTS sections 375371/375373; results entry 375373; crim.txt Sections 1.1/1.2, 2.1/2.2/2.3, Section 3 move rules, Section 4 (Theorems 17--22 including proofs and proof of Theorem 4), Section 5 through Conjecture 6 and surrounding questions; computational-range text and relevant reference links; HTML checked for source identity and predecessor links. Figure captions/algebraic descriptions only, not visually reviewed. Text from initial broad outputs was truncated; the important definitions and complete Section 4 were re-extracted explicitly. read-inventory.json records hashes, with limitations here controlling any generic depth labels.

Current abstract https://arxiv.org/abs/2606.16828: only v1, submitted 2026-06-15 15:09:22 UTC; no later version or journal reference shown. Current explicit https://arxiv.org/html/2606.16828v1 matches frozen crim.html SHA e3098d23dee5d98578d267555e525de617aa4583e61600ea65cb3d9aa1fd4e6f. Conjecture 6 remains conjectural in this body, and Theorem 19 proves just hooks. No claim of all inaccessible versions/corrections being absent.

Printed finite ranges: Section 5 discusses normal P/N status for partitions of area <=50 in connection with Conjecture 1; its table ends at 30. Later text explicitly verifies Conjecture 9 for n<=50. Neither sentence states a CP/Conjecture 6 verification range. No such range was located by reading the Conjecture 6 context and screening the paper's computational/verification language. Do NOT relabel 50 as a tested Conway-pair bound.

Thesis: landing https://repozitorij.upr.si/IzpisGradiva.php?lang=slv&id=19707 says 2023, posted 2023-10-11, English final project, IX+40 pages plus appendices. The advertised Dokument.php?id=28451&lang=slv returned a study-use agreement form, HTTP 200 HTML, not a PDF. One normal form POST was made with its advertised key; it again produced the same 7951-byte HTML. No challenge/auth bypass or alternate route followed. Its body remains UNREAD. This is private study access exploration, not OA or permission to redistribute full papers.

2022 predecessor: paper cites Bašić/Gottlieb/Krnc, Some observations on the Column-Row game, SCORES'22, with DOI text pointing to scores23 (bibliographic inconsistency not resolved). A managed search located the institutional proceedings https://zalozba.fri.uni-lj.si/SCORES2022.pdf and conference mirror. Only search excerpts were seen (normal-play SG/hook work); HTTP retrieval of the institutional PDF did not complete before the capped job was killed. No mirror retry, full-body clearance, or chronology beyond the proceedings' 2022 metadata is claimed.

Bounded managed search queries: '"CRIM" "Conway" "2606.16828"'; '"even-by-even hook" proof'; '"Some observations on the Column-Row game"'. Results routed to the source/abstract mirrors, proceedings, and catalogue entries; no new proof body was read from those results. This is not an exhaustive citing-literature search. Search-service byte/hash/RSS telemetry is unavailable.

## Current registries and prior limits

Current public OpenAI/math landing head: 4eaee87548250b2682affda7d05d947c05554bae. Its pinned CONTENTS.md was retrieved and screened for 375373, 2606.16828, Conway pair, rectair, CRIM. No relevant match: the eight raw 'crim' substrings are in 'discriminant(s)'. This is catalogue routing, not proof-body exhaustiveness. Historical supplied r322 snapshot fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is only dated metadata in registry-screen.json, not a new historical-body read.

Current correct Vilin97/lean-pool landing head: 01db1d7049cf9668bda1e9e106875ee1278b43e6. No target/source keyword in landing text; pinned project/import sources were not freshly fetched. The earlier guess Vilin97/LeanPool returned 404 and was stopped. The correct URL came from the frozen receipt, not an access workaround. Keep the distinct other-repository head 906301dff114598197af816aefe25211ff23a6b0 separate; it was supplied by task and was not refreshed. Frozen projects/imports receipt metadata was read, not a fresh full proof audit. No newly matched proof body to adjudicate. No completed-history allowlist was supplied for this lane beyond the named r322 material, so no other local histories were opened.

## Integrity, exceptions, resources, and artifacts

First actual command was the mandatory bootstrap, unchanged. It set affinity and limits before printing ancestor AGENTS and the entire standalone TASK. Before mathematical reads, all 142 explicitly frozen paths matched; frozen-after.json repeats the full check. Hashing unrelated frozen bytes was integrity-only. No active r324 or crown-vnumber path was read, hashed, globbed, or polled. Only this lane was written; no shared scalar/ledger edits, git, children, Lean, enumeration, solvers, CAS, author/dependency edits, paper, browser, account action, contact, upload or publication.

Scope exception: the initial output command read/printed the complete r322 literal-provenance.json instead of selecting only 375373, exposing unrelated record metadata; later registry/source/corpus inventory reads likewise included unrelated metadata. These were avoidable overbroad metadata reads, not authorized new target investigations. No unrelated mathematical source bodies were opened or acted on. This report does not conceal the exception. Entire results.json had to be parsed to select its keyed entry. Target-only extracts are now saved.

Resource reporting: every later command began with affinity restricted to the first two already-allowed CPUs, CPU limit 120 seconds and AS 6 GiB, using Python -I -B; external command timeouts were 20--100 seconds, under 140. Bootstrap used tighter limits. One fetch batch was reaped by external timeout 100 (exit 124); buffered output and its end-of-job receipt were lost. Thesis-body.html survived, but exact POST completion UTC/status were not persisted; do not invent them. The next planned URL in that batch was the institutional SCORES PDF; completion unavailable. Later batch URLs were not reached (no corresponding outputs), and were fetched separately. No denied route was reset. Initial ordinary jobs' individual RSS/CPU were not instrumented; unavailable. Surviving resource-fetch.json and resource-final-fetch.json measure SELF high-water RSS and SELF CPU only. They do not measure group/cgroup peak or managed search service telemetry. No job remains running; all exec sessions were explicitly reaped before handback.

Artifacts: REVIEW.md, review.json, CHECKPOINT.md, literal-target.json/jsonl, target-provenance.json, inherited-results.json, inherited-literal-provenance.json, read-inventory.json, http-receipts.json, resource reports, frozen-before/after.json, bootstrap receipt, downloaded primary HTML, and manifest.json. HTTP receipts contain exact URL/UTC/status/byte/SHA for completed instrumented fetches. Failed and missing telemetry is listed, not estimated. No accepted credit.
