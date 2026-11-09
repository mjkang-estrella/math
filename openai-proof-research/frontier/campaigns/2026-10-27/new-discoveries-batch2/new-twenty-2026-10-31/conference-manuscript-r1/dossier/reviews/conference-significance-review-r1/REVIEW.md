# Independent adversarial significance review: MathDB 324342 (conference-matrix MDS conjecture)

Reviewer: Claude Opus 5.5, `conference-significance-review-r1`, 2026-11-01 08:32–08:44 UTC (final frozen re-check at 08:43:41: 0 mismatches out of 91).
Candidate packet: `conference-mds-resume-r4` (one candidate; r3 and r4 share one frozen witness and certificate).

## Verdicts

| Gate | Verdict |
|---|---|
| Literal / source / version equivalence | **PASS**, with source corrections listed below |
| Independent ordinary correctness | **PASS** |
| Lean statement reading (not a replay) | **PASS**. The independent Lean/fidelity replay is a separate gate and is still pending. |
| Bounded live prior art / subsumption | **Bounded PASS, with two recorded material gaps.** No public resolution was found, and no theorem with a short bridge to it. Arasu–Gulliver 2001 and Grassl–Gulliver 2008 are closed-access and their bodies are unread. |
| Qualified novelty | **Bounded PASS.** No prior computation of this code was found. Worldwide priority is not certified. |
| **Mathematical significance** | **FAIL.** The refutation reduces to one routine computation on the first non-Paley instance (§5). |

**Recommendation: 0 credit.** The refutation is correct and matches the exact literal scope. But under this campaign's strict bar its mathematical content is a single routine computation, so it is a side conjecture, a computer check and a kernel proof, with no structural advance. This is a review recommendation only. Acceptance and rejection are decisions for root.

**Frozen inputs.** All 91 bindings in `frozen-inputs.json` were checked before the review (08:32:10 UTC) and after it (08:40:44 UTC): 91/91 match and 0 mismatch (`work/frozen-before.txt`, `work/frozen-after.txt`). The review wrote nothing outside this directory.

## 1. Literal statement, source, and versions

**MathDB literal.** Line 3870 of `lanes/root-mathdb-corpus-reconciliation-r307/frozen/mathdb-normalized-chunk-0002.jsonl` (chunk sha256 `d944c503…a0ea`). The line sha256, excluding the trailing newline, is `73a0bb42…1342`, which matches r3/r4. Record 324342:

> Let p be a prime, and let C be a code of length p+1 constructed from a generator matrix that is a conference matrix. The code C is an MDS code of dimension (p+1)/2 and minimum Hamming distance (p+3)/2.

The record also contains an editorial sentence ("This would give … rank over Z_p"). It adds no hypothesis.

**Versions read directly (actual bodies).**

| Version | Date (from the header) | Label | Text |
|---|---|---|---|
| arXiv 1210.5725v1 | 21 Oct 2012 | Conjecture 5 | Same wording. In v1, Theorem 4 has a typo: "order n = p − 1". |
| arXiv 1210.5725v2 | 11 Dec 2012 | Conjecture 5 | Same wording. Theorem 4 reads "n = p + 1". The conclusion lists open problem 2: "Is the code of length p+1, p prime, obtained from a conference matrix of order p+1 an MDS code?" |
| ISIT 2013 (author copy) | — | Conjecture 1 | Same wording |
| IEEE TIT 59(10) 6712–6723, author-posted copy (r4 stream extraction) | Received 11 Dec 2012; revised 16 May 2013; accepted 6 Jun 2013; published online 12 Jun 2013; current version 11 Sep 2013; October 2013 issue. DOI 10.1109/TIT.2013.2268156. | Conjecture 1 | Text is the same with the math glyphs missing. It is preceded by "We believe that a surprising result will be derived if we will examine the Hamming distance of these codes." |

The journal publication is 2013. The "2015" in the URL is only the upload directory, so r4's correction of r3 is right.

**Quantifiers, field and construction.**

- The conjecture quantifies over **every prime p and every conference matrix of order p+1**. Here a conference matrix is the source's weighing matrix W_{n,n−1}: entries in {0, ±1}, exactly n−1 nonzeros in every row and column, and WWᵀ = (n−1)I.
- The code is the row span. Equivalently, it is the reduction of Λ(W) to Z_w with w = p (Theorem 1), which is the same as F_p (Theorem 4).
- **The field is forced.** det W = ±p^{(p+1)/2}, so over any field of characteristic ≠ p the rank is p+1. Only over F_p can the dimension clause (p+1)/2 hold.
- **No Paley restriction exists in the source.** "Verified … where the conference matrices are based on Paley's construction" describes the authors' evidence, and open problem 2 is also unrestricted. Reading the conjecture as Paley-only is not supported by any version.

**Dimension clause.** It holds for every p. It is the source's Theorem 4, and I independently confirmed rank 10 for W20 and for the order-20 Paley matrix. Only the MDS and distance clauses are false.

**Source corrections, for the record.**
1. v1 Theorem 4 says "n = p − 1"; v2, ISIT and TIT say p + 1.
2. Theorem 4's proof ("diagonal with (p+1)/2 p's and (p+1)/2 1's") leaves out why every elementary divisor divides p. The missing step: p·W⁻¹ = Wᵀ is integral, so each elementary divisor is 1 or p. The statement is still true.
3. The clause "minimum Hamming distance (p+3)/2" is redundant once MDS and the dimension are given. Refuting either clause refutes the conjecture.

## 2. Lean statement reading

Source: `conference-mds-resume-r4/lean/ConferenceMDS324342.lean`, sha256 bound in the frozen inputs.

**Fidelity of the definitions.** `Conjecture5` is

∀ p prime, ∀ W : Matrix (Fin (p+1)) (Fin (p+1)) ℤ, IsConferenceMatrix W → IsMDS ∧ finrank = (p+1)/2 ∧ minDistance = (p+3)/2

over `ZMod p`. The pieces match the source:
- `IsConferenceMatrix` is literally the source weighing-matrix definition with w = n − 1.
- `rowCode` is the `ZMod p` span of the rows.
- `minDistance` is sInf over `hammingDist` of distinct codewords.
- `IsMDS` is Singleton equality with `Module.finrank`. The natural-number subtraction is harmless because finrank ≤ n.

**Bridge.** `latticeCode_eq_rowCode` is generic over p, n and W, and it ties the lattice-reduction wording to the row span.

**Endpoint.** `conjecture5_false : ¬Conjecture5` instantiates p = 19 with W20 and uses only `minDistance ≤ 9` together with finrank = 10. The textbook-definition variant, the min-weight variant and the per-clause variants are all also refuted.

**Replay receipts (spot-checked only).**
- `replays/final/build/ConferenceMDS324342.lean` is byte-identical to the packet file.
- `audit.stdout` has 90 `AXIOMS` lines and reports `AUDIT declarations=90 disallowed=0`.
- `forbidden.txt` is empty, and main/checker stdout and stderr are empty.

I did **not** rebuild the Lean file. The independent replay is a separate gate.

**Claim inflation check.** Lean proves only d ≤ 9. The following are ordinary computational facts, **not** Lean-certified, and should not be described as all-Lean:
- exact d = 9;
- self-duality of C;
- the 180 and 6,180 projective word counts.

## 3. Independent ordinary correctness

`scripts/indep_check.py` is my own implementation. It does not import any r3/r4 script or certificate, and it parses W only from the Lean source text. The run was `taskset -c 0,1`, `ulimit -v 4 GB`, `timeout 580`, with 34 s wall time and 11 MB RSS. Output is in `work/indep_check.json`.

Results:
- Entries are in {0, ±1}, every row and column has 19 nonzeros, WWᵀ = 19I, W is skew, and the diagonal is zero.
- The rank over F_19 is 10. The Lean word (weight 9) lies in the row span.
- **Exact d = 9**, found by a different method from r4's. d is the least w such that some (20−w)-set of columns of the RREF generator has rank < 10.
  - There are no deficient sets for w ≤ 8.
  - For w = 9 there are exactly **180** rank-deficient 11-sets.
  - Each such set carries a 1-dimensional space of words: a 2-dimensional space would contain a word of weight ≤ 8. So this count agrees with r4's 180 projective weight-9 words.
- Control: the bordered Paley matrix of order 20 gives rank 10 and d = 11, so it is MDS.

**Routineness probe.** `scripts/gs_routine_check.py` (`work/gs_routine_check.json`, 84 s) is my own Goethals–Seidel array implementation.
- From r4's length-5 sequences it gives a skew conference matrix whose F_19 code has d = 9.
- An exhaustive enumeration of length-5 GS quadruples (a skew-type) finds 12,000 quadruples, all giving distinct matrices.
- **The first 6 distinct GS matrices I tested all give d = 9**. The rest were not tested, which kept the run bounded.
- r3's "2,767" figure remains unverified and is not used.

## 4. Prior art and subsumption (bounded, live)

**Arasu–Gulliver, IEEE TIT 47(5) 2051–2055, 2001, DOI 10.1109/18.930940.**
- Body status: **closed, body unread.** OpenAlex reports `oa_status: closed`, `any_repository_has_fulltext: false`. Semantic Scholar reports `CLOSED`. The Wright State CORE Scholar page (`/math/563`) is metadata only, linking to the DOI or ezproxy. No lawful full text was found, and no paywall was bypassed.
- Abstract (OpenAlex): "codes constructed from weighing matrices, and in particular conference matrices … necessary condition for these codes to be self-dual … examples … lengths up to 40. Codes constructed from all weighing matrices of order n ≤ 13 are also considered."
- **Secondary primary body read:** Armario–Frau, arXiv:1311.2637v1 (11 Nov 2013), §1.2 and §2. It describes the [2]=AG and [7] constructions as the length-2n codes G = [αI, W] with α² + k ≡ 0, and G = [αI, βI + W] (W skew) with α² + β² + k ≡ 0 (mod p), with α and β nonzero. Its AG tables use lengths N = 2n, and "Length 40 was the limit of the search for minimum distance given in [2]."

**Concrete obstruction to AG subsuming the result** (from the secondary description, not from the unread body):
- For k = 19 and p = 19, the [αI, W] construction needs α² ≡ 0, which is impossible for α ≠ 0.
- The [αI, βI+W] construction needs α² + β² ≡ 0 (mod 19), which is impossible because −1 is a non-residue mod 19 (19 ≡ 3 mod 4).
- So the AG constructions, as described, cannot produce *any* F_19 code from an order-20 conference matrix. They also produce length 40, not 20. AG's "all weighing matrices of order ≤ 13" stops below 20.

**Residual material gap:** a remark in the unread AG body about the length-n code when p | k cannot be excluded. Exact missing material: the AG body, especially §2 (Propositions 2.1–2.2, per Armario–Frau) and its tables.

**Grassl–Gulliver, ISIT 2008 pp. 1954–1957, DOI 10.1109/ISIT.2008.4595330.** Closed (OpenAlex and S2); body unread. Abstract: self-dual MDS codes of all even lengths ≤ 2^m over F_{2^m}; self-dual MDS codes of length q+1 over F_q for every odd prime power q; and some new self-dual MDS codes. This bears on the existence of MDS parameters, which is the Paley side. Nothing in the abstract addresses non-Paley conference-matrix codes. **Gap:** body unread.

**Harada–Munemasa, arXiv:1011.5382v2 (6 Apr 2011; JCD 2012), body read.** It uses exactly this object type, row codes of weighing matrices mod p | k, to classify weighing matrices of orders ≤ 15 and 17. Order 20 is not covered, and there are no F_19 order-20 distance data. Not subsuming.

**Ball's theorem (PROOF.md's "from memory" claim), now verified against the primary body.**
- Source read: Simeon Ball, author-posted revised preprint dated 17 Jan 2012 (`web.mat.upc.edu/simeon.michael.ball/jems-mds-conj-revised.pdf`). Published as JEMS 14 (2012) 733–748; the published body is not read.
- Theorem 1.8: if p ≥ k, a set of q+1 vectors of F_q^k with every k-subset a basis is equivalent to Example 1.1, the normal rational curve. The abstract adds: "the longest MDS linear codes, whose dimension is bounded above by the characteristic, are Reed–Solomon codes."
- Here q = p = 19 and k = 10 ≤ p. So a [20, 10] MDS code over F_19 must be a doubly-extended GRS code. PROOF.md's assertion is **correct in substance**, and it is a classification result, not merely the length bound.
- **Correction:** the Ball–De Beule II abstract (arXiv:1201.5994v1, 28 Jan 2012, body read) states only the length bound and cites [1] for the prime case. The classification must be cited as Ball (JEMS 2012) Theorem 1.8, not as "Ball 2012 MDS conjecture".
- It is used below only for the significance assessment, never in the refutation.

**Classification of order 20.** Araya–Harada–Kharaghani–Mohammadian–Tayfeh-Rezaie, arXiv:2402.11074v1 (16 Feb 2024), Table 1 (body read): there are **2** H-inequivalent and **2** SH-inequivalent skew-Hadamard matrices of order 20. That paper quotes this figure as known; it is not its own result.

**Citing works.** The r4 OpenAlex lists gave 13 citing works for TIT, 3 for ISIT and 0 for arXiv. I fetched and grepped the bodies of the three with arXiv copies:
- 2303.16879 (Lattice Constructions D/D′);
- 2207.08031 (MWS/FWS codes);
- 1412.5797 (Quasi-perfect Lee codes).

None mentions conference-matrix codes or the MDS conjecture; EVY appears only as a reference. The other 13 are title-screened only. This is **not** a global clearance.

**Web searches** (standard, 08:33–08:38 UTC):
- the AG title;
- conference matrix / GF(19) / skew order 20 / self-dual;
- the GG title;
- Ball classification;
- conference-matrix / Reed–Solomon mod p;
- "Etzion Vardy Yaakobi conference matrix MDS conjecture counterexample";
- skew-Hadamard order-20 classification;
- Ball's JEMS title.

No resolution of, or counterexample to, Conj 5 / Conj 1 / open problem 2 was found.

**Registry.**
- I reused `intricacy-parent-final-r1/registry-head-receipt.json` (sha256 `b5c48ae7…b628`). It records openai/math head `4eaee87548250b2682affda7d05d947c05554bae`, verified 2026-11-01T08:24:36Z, with commit date 2026-10-30T00:35:35Z. Its scope is head verification only.
- r4's path screens (CONTENTS, history, README, and the complete preprints subtree at that head; root tree truncated) show no hits. Bodies of the full tree were not cleared.
- MathDB state is known only up to 04:46 UTC (0 solutions). Palomar returned the inherited 403 or empty results. Neither was retried.

## 5. Significance: adversarial assessment

**Ordinary reduction (why FAIL).** Each step uses only existing public material plus one standard computation.

1. **The conjecture is an implausible rigidity claim.** By Ball (JEMS 2012, Thm 1.8), an MDS [p+1, (p+1)/2] code over F_p is a doubly-extended GRS code. So the conjecture, given Theorem 4, is equivalent to: *every* conference matrix of order p+1 has a GRS row span mod p.
2. **The source's only evidence is a structural tautology.** Paley matrices give doubly-extended RS codes (χ(j−i) ≡ (j−i)^{(p−1)/2}). That fact explains the n ≤ 23 checks and says nothing about non-Paley matrices. r4 itself classes this as routine.
3. **Order 20 has exactly one non-Paley candidate class.**
   - Every conference matrix of order ≡ 0 mod 4 is equivalent to a skew one. This is a classical fact, read here only as Theorem 1.1 of Armario–Frau, which cites the CRC Handbook of Combinatorial Designs (1996), p. 497. I did not read the original attribution.
   - Equivalent matrices give monomially equivalent codes.
   - There are exactly 2 SH-classes of skew-Hadamard matrices of order 20 (Araya et al., Table 1).
   - So at most two code classes occur at order 20: the Paley one, with d = 11, and one other.
   - W20 lies in the other class, because its d differs from Paley's. Hence **every** non-Paley conference matrix of order 20 refutes the conjecture. This is a bounded inference from the secondary table, not Lean.
   - Order 20 is plausibly the smallest prime+1 order with a non-Paley class. r4 makes no minimality claim, and I did not audit the classifications for orders ≤ 18.
4. **Finding and checking the counterexample takes no new idea.**
   - A non-Paley skew conference matrix of order 20 is a textbook object: the standard Goethals–Seidel array with length-5 sequences. I cite this from general knowledge; the original 1970 paper was not read.
   - My first six GS instances all gave d = 9.
   - The minimum distance of a [20, 10] code over F_19 takes seconds by brute force (34 s here in pure Python) and is instant in Magma.
   - There was no search difficulty and no all-choices quantifier, unlike the accepted 388087 case, where an all-choices obstruction over a 6,517-leaf tree carried the substance.

**Strongest case for PASS, and why it does not survive.**
- *It settles exactly a conjecture that has been explicitly open in IEEE TIT since 2012–2013 and is listed as an open problem.*
  - True, but the open status reflects neglect, not difficulty: 16 citing works, none engaging the question.
  - The settlement is the first test anyone would run.
  - The campaign rule says an open label, a side conjecture, a computer search or a kernel proof alone is not significance.
- *The authors expected a "surprising result".* The wording is ambiguous: it can also be read as expecting surprisingly good MDS codes. Either way it is not evidence of depth.
- *It sharpens a Paley versus non-Paley dichotomy.*
  - Only the Paley half is a theorem, and it is routine and excluded.
  - The non-Paley half is shown for one class at one order. The packet proves no general statement, such as "row code MDS ⟺ Paley-equivalent" or "non-MDS for all non-Paley W of order p+1".
  - A general theorem of that kind would be a substantive candidate. This packet does not contain one.
- *It is fully explicit and Lean-certified.* Certification and explicitness establish correctness, not significance.

**Decision.** Significance is **FAIL** (routine) under the campaign's strict bar. This is not a subsumption FAIL: I found no prior publication that states the result, so novelty stays a bounded PASS. The FAIL does not depend on the unread AG/GG bodies. If either of them did contain the computation, the verdict would only gain a subsumption ground.

**What would change the verdict.** A proof of a structural statement would be a materially different candidate. Examples:
- "For every prime p ≡ 3 mod 4 with p ≥ 19, some skew conference matrix of order p+1 has a non-MDS F_p code."
- A characterization of conference matrices with GRS row codes.

That would be a new candidate and was not assessed here.

## 6. Limits

- AG 2001 and GG 2008 bodies are unread because they are closed-access; secondary descriptions and abstracts only.
- The TIT body comes from a damaged author PDF with no math glyphs. The publisher version was not accessed.
- Ball's classification was read in the author's revised preprint (17 Jan 2012), not the JEMS typeset version.
- The order-20 SH count comes from a 2024 survey table that cites earlier classification work. I did not re-derive it.
- Only 3 of the 16 citing-work bodies were inspected.
- MathDB state is known only to 04:46 UTC. Palomar's 403 was respected.
- The registry receipt is head verification only.
- I did no Lean rebuild. Exact d = 9 and the self-duality/projective counts are ordinary computations.
- No worldwide-priority certification. The 0-credit recommendation is pending root.

**Receipts.** `work/fetch.log` records UTC, HTTP code, URL and sha256 for 14 single fetches into `web-untrusted/f1/`, all HTTP 200. No endpoint was retried, there was no browser, no upload and no external message.

**Resources.** Both Python runs were `taskset -c 0,1`, `ulimit -v 4 GB`, `timeout 580`. No background jobs are left.
