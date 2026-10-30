# Independent manuscript audit, round 1

**Verdict: REVISE.**

Theorem A and Corollary B need no mathematical repair, and the quantifiers stay as stated. Three required repairs are documentary: the product-novelty sentence, the formal-status paragraph, and the public verifier. This review does not accept the candidate, does not change the campaign count, and does not certify worldwide priority.

Author of the mathematics: Myeongjin Kang, no affiliation. Original review prose: CC BY 4.0. Original review code: MIT. Third-party rights stay with their sources.

Frozen manuscript read in full: `kn-minus-edge-manuscript/main.tex`, 603 lines, 54,602 bytes, SHA-256 `a70f6090a3040d136e7799bd6746acc1f9f7cf7c9a66c23635a8cc1b24a1e0b6`. PDF: 15 A4 pages, 160,706 bytes, SHA-256 `99437882b7daf2f6d6eef1ef9fcb021084126d6537fb8606da85bf921d6fd921`. Output manifest: 9,977 bytes, SHA-256 `2c8b828f5a556b4d4c2aad8ba2525aba17af67af2767f97ba6c7d77b5ee27254`. All three match the pins in the assignment.

## Required fixes

### R1. Product novelty omits the path length. Severity: attribution.

The equality of Corollary B is proved for every `m >= 4` and every `n >= 1`, with `P_n` the path of `n` edges. That statement should stay. The repeated sentence that the consequence is new exactly for odd `m >= 13` is too wide.

Ouyang–Wang–Huang Corollary 5.1 is the equality

`cr(K_m □ P_n) = (n-1) cr(K_{m+2} - e) + 2 cr(K_{m+1})`.

At `n = 1` the coefficient of the minus-edge term is zero, so the identity is `2 cr(K_{m+1})`. After Premise U5 that is `2 Z(m+1)` for every `m >= 4`, including odd `m >= 13`. The new odd lower bound is not an input. The proof already records the drop-out (`main.tex` lines 482–483; PDF page 12). The novelty sentences do not.

The new bound enters only when `n >= 2` and `m+2` is an odd order at least 15, that is odd `m >= 13` and `n >= 2`. Concrete values: `Z(14) = 315`, so `m = 13`, `n = 1` gives `630 = 2 Z(14)`. For `n = 2` the same base gives `420 + 630 = 1050`. Substituting the OWH Theorem 3.1 ceiling `419` at order 15 instead of the new value `420` yields `1049`. That one-crossing gap is why `n >= 2` matters.

The same qualification belongs everywhere the package calls the product new, together with the bounded-search limit already stated in Section 7. Locations:

- `main.tex` line 61, abstract, PDF page 1: “This consequence is new for odd `m >= 13`.”
- `main.tex` lines 112–113, Section 1.1, PDF page 2: “Corollary B is new exactly for odd `m >= 13`,” explained only by availability of `cr(K_{m+2}-e)`.
- `README.md` line 10.
- `metadata.json`, field `scope.new_part`.
- `source-to-claim.md`, claim-map row for the novelty boundary.
- Section 7, which states the bounded search for the odd complete case and should state the same limit for the product.

Section 7’s limit is: the October 2026 search found no earlier proof of odd `n >= 15`, and that search is not a priority certificate. The abstract and Section 1.1 currently state the product as new with no such limit. Repair the wording. Do not narrow Corollary B.

The matching product upper bound, for odd `m >= 13` and `n >= 2`, already follows from the classical Zheng upper bound on `cr(K_{m+2}-e)`, Corollary 5.1, and Harary–Hill. The new input on that range is the matching lower bound. One sentence to that effect is enough; it is part of this required qualification, not a second theorem.

### R2. Formal status is stale. Severity: coverage documentation.

Section 9 (`main.tex` lines 526–528, PDF page 14), `formal-scope.json`, `README.md` line 12 and line 57, `metadata.json` (`formal_proof_available`, `formal_status`), `response-to-findings.md` item (6), and `source-to-claim.md`’s closing sentence say that no machine-checked proof of any lemma exists and that the intended formal scope has not been implemented or audited. That was the state when this manuscript was frozen. It is no longer the state of the separate formal directory.

`kn-minus-edge-formal-v1/KnMinusEdge.lean` is 804 lines, 36,557 bytes. It contains 47 theorems and 17 definitions, 64 declarations in total, including `@[simp] theorem diagonalForm_apply`. `Controls.lean` is 104 lines, 4,779 bytes, with 9 theorems. Those byte sizes match the formal review. `kn-minus-edge-formal-review-r1/review.md` is 19,038 bytes, SHA-256 `bbb0344dda8194ef776a8c4bc68a8d44894e6cee178fe019a78cfd962f4d3773`, verdict `PASS_SCOPED_SUPPORT`, required fixes none. Its `ReviewControls.lean` contains 16 theorems. `coverage.json` and the formal README describe the same boundary. The parent file `formal-review-r1-disposition.json` records a later replay; this audit did not recompile Lean and does not recertify that compiler run.

The revision should replace “unimplemented and unaudited” with the scoped result, and it should keep the crossing theorem as a paper claim. Accurate current scope:

- Machine-checked algebraic support exists for the tensor-kernel decomposition, the first-slot dimension `d^2-d`, the weighted diagonal form, the `P Q Delta` degree and missing-pair identities, the twisted rectangular detector with U4 passed in as an explicit hypothesis, the local-test degree budget, Lagrange isolation, the `2s-1` versus `2s-4` root count, and generic cancellation and descent tools.
- Still paper-only: graph topology and cycles; barycentric cycle boundaries; local drawing-sum identities; identification of abstract local nodes with the global complete-star nodes (`hidentify` and `htests` are obligations, not upstream premises); substitution of `P(x,u,x,v)` and the four prime factors in the multivariate ring; instantiation of descent on the actual evaluation kernel; both evaluation injections, including the slot swap; the ordered-pair factor of 4 and `c(D) >= |T|/2`; the even responsibility argument; the upper drawing; all-`n` assembly; Corollary B and OWH Corollary 5.1.
- U4 nonsingularity is a theorem argument in Lean, not a proof of the pinned upstream lemma and not a new axiom.
- No declaration in the formal package states Theorem A or Corollary B.

`formal-scope.json` should point at the formal package and the formal review hash, list the 47 / 64 / 9 / 16 counts, and keep `machine_checked_theorem_claimed` false. Do not describe this as a certificate of the crossing theorem.

### R3. The public verifier cannot check a clean extraction. Severity: reproducibility.

`python3 -B support/verify_package.py` on the full handoff directory returns `VERIFY PASSED`, and with `--with-inputs` it also returns `VERIFY PASSED`. The public ZIP does not contain itself, `output-manifest.json`, or `SHA256SUMS`. The README inside that ZIP tells a reader to run the same command.

On a clean unzip of `kn-minus-edge-manuscript-public.zip` the verifier crashes, rather than printing `VERIFY FAILED`:

1. With only the extracted files it raises `FileNotFoundError` for `kn-minus-edge-manuscript-public.zip` (`verify_package.py` line 46).
2. After the ZIP is copied in beside the extraction, it raises `FileNotFoundError` for `output-manifest.json` (line 52).
3. After a stand-in `output-manifest.json` is added, it raises `FileNotFoundError` for `SHA256SUMS` (line 53).

Transcripts: `receipts/clean-verify-1.txt`, `clean-verify-2.txt`, `clean-verify-3.txt`.

Repair: add a public mode that checks the extracted members against `public-manifest.json` and does not require the handoff manifest, `SHA256SUMS`, or a copy of the ZIP. Keep the current full-directory check. Missing files should be reported as a failed verification. Document both modes and record one clean-extraction test. The allowlist itself is the right boundary: 39 ZIP members, no `work/`, no page renders, no third-party PDF, no upstream source, and no survey extraction.

## Scope that stands

Theorem A: for every integer `n >= 2` and every edge `e` of `K_n`, in the ordinary crossing number,

`cr(K_n - e) = Z(n) - binom(floor((n-1)/2), 2) = (1/4) floor((n+2)/2) floor((n-1)/2) floor((n-3)/2) floor((n-4)/2)`,

with the parity forms in (1.2). Corollary B: the displayed floor formula for every `m >= 4` and every `n >= 1`, one application through OWH Corollary 5.1. The new complete-graph range remains the odd lower bound for `n >= 15`. Even orders, odd orders `n <= 13`, and the upper bound remain classical once Harary–Hill is granted. No quantifier was narrowed.

## Interfaces

Pinned OpenAI source, commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, file `preprints/The-crossing-number-of-complete-graphs-September-23-2026/build/main.tex`, 40,122 bytes, SHA-256 `5ae2c60704054f1b45290463c038c32335cc1554c5cc7dcee53518a045472301`. Upstream truth is stipulated. The statements used match the local copy:

- U1, `lem:normalization`, lines 850–854: every finite simple graph has a normalized minimum drawing.
- U2, `eq:J` line 222 and `lem:cycles` lines 231–233, under the normalized-drawing setup at lines 188–193. The proof says the argument applies to every finite simple graph. The paper applies it to `K_n - e`.
- U3, `lem:weights`, lines 362–369: degree at most `N-2`.
- U4, `lem:detector` lines 443–446, first sentence only: `M` is nonsingular on `P_{s-1,s-2} × P_{s-2,s-1}`. Lines 447–451 are the square consequence, which the twisted test does not fill. The paper uses the rectangle.
- U5, `thm:main`, lines 117–126: `cr(K_n) = Z(n)` for `n >= 3`.
- U6, Section 5 and `prop:upper` lines 766–768, with the semicircle rule at lines 720–727: above when `(i+j) mod n < floor(n/2)`, crossings are the same-side alternating pairs, total `Z(n)`.

OWH was read in `fresh-substantial-discovery-r2/sources/literature/owh-2014-sciencedirect-fetch.txt`, the ScienceDirect text, not the publisher PDF. Corollary 5.1 (around the rendered lines 308–314) is the equality for `m >= 4`, `n >= 1`. The path convention (around line 264) is length `n`, vertices `0,...,n`. Theorem 5.1’s `n = 1` case is `2 cr(G+K_1)`, and Theorem 5.2’s `n = 1` case is the matching lower bound, so the minus-edge term is absent before any new work. `K_m + 2K_1` is `K_{m+2}` minus the edge between the two new vertices, and `K_m + K_1` is `K_{m+1}`. For `m >= 4`, `K_m` is vertex-transitive and has four dominating vertices, which is what Theorems 5.1 and 5.2 ask for. The zip-product chain, Bokal’s lemma, and the identification left to the reader inside Theorem 5.2 are cited and were not re-audited. The paper says so. Theorem 3.1’s displayed bound matches the formula used in Section 7.

## Proof reading

The odd argument was read equation by equation. These steps close.

Lemma 3.1 is sufficient. The tensor decomposition kills both slots of `φ`, the coefficient of `[ab]` in `z_A` is `w_a w_b φ(A)`, the boundary vanishes by U3 for degree at most `n-2`, and U2 gives `Σ(H) = 0` on `G = K_n - e`. Remark 3.2’s `H = xy` violates both identities and satisfies `Σ(xy) = J̃(z_x, z_x) = 0` by skew-symmetry. There is no converse.

`dim Sym = binom(s,2)`, checked by the basis count for exponents `0,...,s-2`. Then `dim S_a = dim S_b = d^2 - d` and `dim(S_a ∩ S_b) = (d-1)^2`. The intersection is short of the target by `d-1`, as Remark 3.8 says. `c(D) >= |T|/2` is the right direction: repeated crossings and sign cancellation only weaken the inequality.

In Lemma 3.4, `Δ` has degree 3 in each variable, so `PQΔ` has degree at most `2(s-2)+3 = n-2`. Swapping an endpoint orientation negates both `J` and `Δ`, so `a_α` is independent of orientation and nonzero on four distinct labels. The four orientations contribute the factor 4. The diagonal form has nonzero entries. The coordinate for the swapped ordered pair carries `-a_α`; that coordinate is a different element of `T`, and the form stays nondegenerate.

Lemma 3.5 rewrites `M(A,(v-u_c)B')` as `M(B',(v-u_c)A)` and invokes the rectangle on `P_{s-1,s-2} × P_{s-2,s-1}`. Cancellation is in the polynomial ring, not at a node. The square consequence does not apply.

Lemma 3.6’s degree budget is `2s-1 = n-2` in each variable. The `v`-budget is degree `s-2` from `P`, three linear factors, and degree at most `s-2` from `B'`. The two twist factors kill the two second-slot orders. The factors `(u-v)(u-y)(v-x)` leave only the star terms `i = k`. For `i` outside `{a,b}` the star is complete, adjacent edges do not cross, and both outward orientations give `J = S_i`. The terms at `a` and `b` are not interpreted; the Lagrange polynomial of degree `2s` vanishes at those nodes. Products `U(t)(t-t_a)V'(t)` span the polynomials of degree at most `2s` that vanish at `t_a`. The diagonal `P(x,u,x,v)` has degree at most `2s-4` and `2s-1` roots, so `C = (x-y)(x-v)(u-y)(u-v)` divides `P`. For `s = 3` the degree obstruction is immediate. For `s >= 4`, `C(t_a,t_b,y,v) = (t_a-y)(t_a-v)(t_b-y)(t_b-v)` is a nonzero polynomial, so the quotient stays in `S_a` and in the kernel, with smaller `x`-degree. The `S_b` injection is the slot swap. Proposition 3.7 then gives `|T|/2 >= d^2 - d`. The case `s = 2` is the zero bound.

The even proof matches OWH Theorem 3.2. The type count (4.1), the restored drawings (4.2), and the responsibility bound (4.3) eliminate `Σ c_i - Σ m_i` with the correct inequality direction, and `l_1, l_2 >= 0` may be dropped. The `m_i` cancel, so no upper bound on them is required. Adjacent crossings in `D_i` can be removed without raising the crossing count, so `c(D_i) >= Z(n)` still applies; the paper’s sentence is enough. With `Z(2M-1) = (1/4)(M-1)^2(M-2)^2`, the bound simplifies to `(1/4)(M^2-1)(M-2)^2`.

The upper bound deletes `{0, t}`, `t = floor((n-1)/2)`, from the U6 drawing. For odd `n = 2s+1` the edge lies below and carries `binom(s,2)` crossings. For even `n = 2s` it lies above and carries `binom(s-1,2)` crossings. Both counts were recomputed from the side rule, not only read off.

Assembly covers `n = 2, 3` by the zero formula, `n = 4` by the zero target, odd `n >= 5` by Proposition 3.7, even `n >= 6` by Proposition 4.1, and `n >= 4` from above by Proposition 5.1. The floor, parity, and product algebras agree, including both parities of Corollary B. OWH’s published table for `cr(K_m - e)` through `m = 12` matches the formula: `0,0,2,6,15,30,54,90,140` for orders 4 through 12.

Section 7’s three gap identities were recomputed for every odd order through 401. The OWH 3.1 deficit equals `(s-1)(s-2)/(2(2s+1))`. Integrality meets the target exactly for `n` in `{5,7,9,11,13}` and misses at `n = 15` (`2720/13` at order 13, ceiling `419` against target `420`). The Theorem 3.2 odd-order gap and the vertex-deletion gap match the printed fractions. Those identities bound three classical routes. They are not a claim that no other argument exists.

Prior findings (1)–(5) and (7) are handled in the paper: sufficient-only Lemma 3.1, the full odd-case components, the credits for OWH, Chia–Lee, Zheng through OWH and the CHN survey, and Sadhu as a bipartite antecedent with different operations, separate arithmetic kinds in Table 2, integer division in the release checker, and hashes with third-party text kept out of the ZIP. Finding (6) is the stale formal paragraph in R2. The contribution review’s phrase “the first product order that uses the new lower bound is odd `m >= 13`” is refined by R1; that frozen review stays unchanged.

## Checks

`support/release_checks.py` is 493 lines. It records failures and exits 1; `-O` does not disable `check()`. Mathematical operations are `//` and `fractions.Fraction`. `time.monotonic` is used only for the runtime stamp.

This audit reran that script, writing only under this review directory. Python 3.14.7, exit 0, stderr empty, runtime 69.6 s. Stdout is byte-identical to `checks/release_checks.out` (590 bytes). Assertion counts: R1 10,501; R2 159; R3 1,498; R4 1,185; R5 4,765; R6 64; R7 25; R8 105; R9 10. R8 and R9 enforce the twist-factor and `H = xy` controls. R6 checks the rectangular rank `s(s-1)` and the twisted rank `(s-1)^2` for `s <= 5` and every twist node.

`checks/independent_algebra.py` recomputes the same closed forms, gap identities, product substitution for `4 <= m <= 200` and `1 <= n <= 20`, the `n = 1` reduction, and the two-page deletion count for `4 <= n <= 30`, without importing the manuscript checker. The rerun in this directory exits 0. Stdout is `receipts/independent-algebra.out`.

The inherited mod-`p` script prints `SOME FAIL` and then ends, so a failing run still exits 0 (`kn_minus_e_modp_large.py` lines 96–109). `run_all.py` rejects any stdout line containing `FAIL`, including `SOME FAIL` with exit 0, and its self-test covers that case. The 20-minute NumPy rerun was not repeated. The retained `checks/author-modp.out` (526 bytes, SHA-256 `906e51acbe8425a182f099fba8e8584ea898cd47bd98e773dbcb62dd95b125a8`) is the orders 15, 17, and 19. Each of its 7 lines occurs in the frozen log `kn_minus_e_modp_large.out` (1,204 bytes, SHA-256 `35f2508e427869ad5a4f9825e63869d03c6ef0377e437eba21e31f23165df20f`), which also contains orders 13, 14, 16, and 18. `checks/run-receipt-large.json` reports exit 0, 1,196.5 s, NumPy 2.5.4, and `lines_match_frozen: true`. That receipt was inspected, not re-executed. The author receipt `checks/run-receipt.json` reports the earlier full runner at 71.7 s plus the inherited author and reviewer checkers; this audit reran only R1–R9.

Finite checks remain support. They do not prove the theorem for all `n`.

## Package and pages

`verify_package.py` on the frozen directory passes, including every `input-manifest.json` hash. The ZIP has 39 members and matches the allowlist plus `public-manifest.json`. `work/chn-v5.txt` is a local survey extraction and is outside the ZIP. SHA256SUMS covers the handoff files and the output manifest; the output manifest excludes itself and SHA256SUMS. That full-directory arrangement is consistent. R3 is the missing public-only mode.

All 15 pages were rasterized here at 120 dpi to `qa/pages/page-01.png` through `page-15.png` and read as images. An ink probe in the outer 0.3 inch of each page is clear. The build log has 0 overfull boxes and 0 undefined references. Three underfull boxes remain, at `main.tex` lines 135–136 (badness 1242 and 10000) and 177–178 (badness 1152), in the commit-hash and bibliography-pointer paragraphs. They widen word spacing inside the measure. Table 1 (page 5), Table 2 (page 13), the degree array (page 8), and the bibliography (pages 14–15) sit inside the margins. Section 9 starts at the top of page 14. PDF metadata: title and author as in the paper, producer xdvipdfmx, 15 pages, A4, unencrypted. No visual repair is required.

## Optional

- The release-checker header and `support/PROVENANCE.md` say the file uses no floating point. The arithmetic does not. The runtime stamp uses `time.monotonic`.
- The title page names Myeongjin Kang and does not add an affiliation. `metadata.json` already has `"affiliation": null`.
- `metadata.json` dates the draft 2026-10-16. The reproducible PDF creation time is 15 October 2026 from `SOURCE_DATE_EPOCH=1792108800`, as the README says.

## Inventory

`input-manifest.json` records the SHA-256 and byte size of every input this audit authenticated. `output-manifest.json` records every file in this review directory except itself and `SHA256SUMS`. `SHA256SUMS` covers the output-manifest entries and `output-manifest.json`. `provenance.json` records the review role, the verdict, and what was not rerun.

## Limits of this audit

Lean was not rebuilt. The 20-minute mod-`p` run was not repeated. OWH’s zip-product proof and Bokal’s lemma were not re-proved; the cited corollary statement was checked in the ScienceDirect text. Zheng’s article was not opened; the manuscript already says it was not. Chia–Lee’s scan was not re-read; the manuscript’s attributions are the ones the source map limits to the pages it read, and they are used as credits, not as proof inputs. Sadhu’s lemmas were not re-proved. No priority search was added. Nothing in the manuscript directory was edited. Nothing was staged, committed, uploaded, submitted, or counted.
