# Independent significance adjudication r2: MathDB 324342 (conference-matrix MDS conjecture)

Reviewer: Claude Opus 5.5, `conference-significance-adjudication-r2`, 2026-11-01 (UTC). This is a single bounded adjudication. It is not acceptance, it changes no count, and it makes no worldwide-priority claim. Candidate credit stays 0 and the campaign stays at 2/20.

## Recommendation

**Significance: QUALIFIED PASS. This is a minimum-threshold pass, limited to the exact-scope finite refutation.** The first reviewer's FAIL does not survive under the campaign's actual written standard and its applied precedents:

- No known theorem, construction, bound or generic reduction yields the refutation. I checked for one and the first reviewer supplied none.
- The FAIL's remaining grounds are ease, runtime, the absence of an infinite theorem, and inferred neglect. None of these is an exclusion in AGENTS. Two of them are not established facts.

**Novelty: bounded PASS, with one disclosed material gap.** The Arasu–Gulliver 2001 (AG) body is unread. This gap is of the same kind as the unread Lütolf–Margot catalogue that 388087 was accepted with. I do not consider it blocking under that precedent. If root requires direct body clearance for AG, novelty, and only novelty, becomes HOLD (§5). The Grassl–Gulliver 2008 gap is weaker: its abstract is about existence of MDS codes, the Paley side.

**What credit should be described as.** If root accepts, the credit is for "an explicit order-20 conference matrix whose F₁₉ row code has a nonzero word of weight ≤ 9, which refutes the Etzion–Vardy–Yaakobi conjecture in its exact universal scope." The following are not part of the credited endpoint:
- exact d = 9 and the 180/6,180 word counts (ordinary computation only);
- the Paley/Reed–Solomon fact (known, routine);
- the order-20 two-class dichotomy (§3; it rests on a secondary classification table);
- minimality of p = 19 (not established).

**Frozen inputs.** All 130 bindings matched at 08:49:12Z, before any reading (`work/frozen-before.json`), and again at 13:02:42Z (`work/frozen-after.json`). I wrote only inside this directory.

## 1. The standard actually applied

**Written rules.** The ancestor batch AGENTS (lines 33–36) says:

> Prefer small exact counterexamples and short full-scope constructive proofs; do not equate shortness with routine adaptation or presume eligibility from an open label.

The written zero-credit exclusions are: a known theorem; a public proof or refutation; a routine corollary; mere formalization; a wording, domain or endpoint correction; a helper; a parameter instance; and a variant of a credited family. The new-twenty AGENTS adds: "A closed proof alone does not establish novelty or significance."

Several phrases the first reviewer cites as a "campaign rule" do not appear in any AGENTS file I found:
- "side conjecture";
- "computer search";
- "kernel proof alone is not significance".

A grep of the frontier tree finds "side conjecture" only in the r4, r1 and revision documents for this candidate.

**Applied precedents (read directly).**

| Precedent | Outcome | Basis |
|---|---|---|
| 388087 Király (`kiraly-significance-review-r1/REVIEW.md`) | PASS | "A finite search followed by an exact certificate is not automatically routine… certificate size and the lack of an elegant proof do not make it significant: the consequence for the named conjecture does." Known existence, catalogue and classification facts "do not resolve the additional … quantifier". |
| 325519 spectral (`spectral-final-disposition.json`) | FAIL | An independent **complete generic routine reduction** (pigeonhole/irreducibility cardinality) refutes the same universal without the witness. The k = 5 witness "supplies no separate sharpness or classification endpoint." |
| 337160 dual polar (`dual-polar-source-review-r1/REVIEW.md`) | FAIL | The counterexample was a direct evaluation of an **already published explicit eigenvalue formula**, an "omitted small location exception" that leaves the main unimodality assertion intact. That review states: "This is not a universal rule that all finite spectral counterexamples lack interest", and it cites accepted Keith, trigonometric and Yuster counterexamples. |

So the precedents exclude a finite counterexample in two situations:
1. an explicit standard reduction, formula or theorem produces it, or makes the universal fail trivially;
2. it only corrects an exception while the main claim survives.

Neither situation applies here (§4).

## 2. Verified prior-theorem chain

All items below were read from cached primary bodies under `conference-significance-review-r1/web-untrusted/f1/`, with the hashes recorded in that review's fetch log. I made no new network requests.

**(a) Ball, author-revised preprint dated 17 Jan 2012 (`ball-jems.txt`); published JEMS 14 (2012) 733–748, typeset version unread.**

- **Theorem 1.8:** "If p ≥ k then a set S of q+1 vectors of the vector space F_q^k, with the property that every subset of S of size k is a basis is equivalent to Example 1.1." Example 1.1 is {(1, t, …, t^{k−1})} ∪ {(0, …, 0, 1)}.
- **Corollary 9.2:** "If p ≥ k then a linear maximum distance separable code over F_q of dimension k and length q+1 is a Reed-Solomon code."
- **Equivalence** (p. 3): "change of basis and field automorphisms". The proof also rescales individual vectors. For codes this means a change of generator matrix plus column scaling and reordering, that is, monomial equivalence. Field automorphisms are trivial over F₁₉.
- **Exceptions:** none for k ≤ p. The p = 2 hyperoval exception needs k = 3 > p.
- **Applicability:** q = p = 19, k = 10 ≤ p, length 20 = q+1. So any MDS [20,10] code over F₁₉ is monomially equivalent to the doubly extended RS code.
- **Timing:** the result predates EVY v1 (21 Oct 2012).
- **Kind of result:** it is a classification, not only a length bound. The Ball–De Beule abstract states only the bound. The first reviewer's citation correction is right.

**What Ball does and does not do here.** The refutation does not need Ball: d ≤ 9 < 11 follows directly from the explicit word. Ball only shows that the conjecture, together with the source's Theorem 4, is equivalent to "every conference matrix of order p+1 has a GRS row code mod p". It says nothing about the code of W20. It does not make non-GRS-ness a corollary, and it does not make the conjecture implausible in any proved sense. The first reviewer's "implausible rigidity claim" is a heuristic, not a reduction.

**(b) Paley case.** The rows are (x − i)^{(p−1)/2} evaluations, so the code is doubly extended RS (revision PROOF.md §3). This is routine and known. But it is the *true* part of the conjecture, and it has no bearing on whether the *refutation* is routine.

**(c) Equivalence transport from Hadamard classes to codes.** I checked this independently, because the objection is correct that inequivalent matrices need not have inequivalent codes, and conversely.

1. Every conference matrix of order n ≡ 0 (mod 4) is equivalent (PWQ, with P and Q signed permutations) to a skew one. This is Armario–Frau arXiv:1311.2637v1, Theorem 1.1, citing the CRC Handbook (1996), p. 497. It is classical (Delsarte–Goethals–Seidel), but I did not read the original.
2. If C is a skew conference matrix, then H = C + I is skew-Hadamard: (C+I)(C+I)ᵀ = 19I + C + Cᵀ + I = 20I, and H + Hᵀ = 2I.
3. Araya et al., arXiv:2402.11074v1, p. 2, define SH-equivalence as "Y = PᵀXP" with P a signed permutation. This is **not** H-equivalence PXQ. If H' = PᵀHP, then C' = H' − I = PᵀCP.
4. Row space(PᵀCP) = row space(CP), since Pᵀ is invertible. Row space(CP) is a monomial image of row space(C).
5. Table 1 of Araya et al. gives 2 SH-classes of skew-Hadamard matrices of order 20; Table 2 gives skew types (1,1) and (1,2). Both are quoted from [8] Hanaki–Kharaghani–Mohammadian–Tayfeh-Rezaie, JCD 2020, which I did not read.

Together these give at most 2 monomial classes of order-20 conference row codes. The H-equivalence count would not suffice, because PHQ does not preserve the structure H − I; the SH count is the one needed, and it is also 2.

The Paley order-20 matrix (19 ≡ 3 mod 4) is skew and gives d = 11. W20 gives a word of weight 9 (in Lean). Hence the two lie in different classes, and **every conference matrix of order 20 is equivalent either to Paley's (MDS) or to W20 (not MDS).**

This is a **new inference**, combining the classification with the new d ≤ 9 calculation. It is not a prior refutation, and no source I read states it. It is bounded: it depends on a secondary table and a classical normalization that I did not re-derive.

**(d) Arasu–Gulliver 2001 and Grassl–Gulliver 2008.** Bodies unread; see §5.

## 3. Claim-by-claim review of conference-significance-review-r1

| r1 claim | Adjudication |
|---|---|
| Literal/source PASS, and the TIT version has "same wording with the math glyphs missing" | **Corrected.** Fidelity is cached and limited: the three fully readable statements (arXiv v1/v2 Conj 5, ISIT Conj 1) agree. The damaged TIT author copy supports the presence of the conjecture but not a parameter-level verbatim comparison. This agrees with `conference-fidelity-review-r1` and the revision. "Same wording" overstates it. |
| Ball Thm 1.8 makes MDS [20,10]₁₉ GRS; it is a classification | **Supported** (§2a): hypotheses, equivalence, absence of exceptions and timing all verified. **Qualified:** it is not used by, and not needed for, the refutation. It gives no reduction that produces the counterexample. |
| The Paley code is GRS, which is routine | **Supported**, but it is the true half and irrelevant to whether the refutation is routine. |
| Exactly 2 SH classes at order 20, so every non-Paley matrix refutes | **Supported after an independent transport check** (§2c), with explicit dependence on the PᵀXP definition and the skew normalization. It is a new derived dichotomy, not prior art. Inequivalence of matrices alone would not imply a non-GRS code. r1 in fact deduced inequivalence *from* d, which is valid. |
| "The non-Paley matrix code fails" | Supported: Lean gives d ≤ 9, and two independent ordinary checks give d = 9. |
| The first 6 Goethals–Seidel instances give d = 9 within seconds | **The facts are accepted, but they do not support FAIL.** By §2c every non-Paley order-20 matrix necessarily gives d = 9, so 6/6 adds nothing beyond class membership. Ease and runtime are not exclusions under AGENTS or under the 388087 precedent. |
| No infinite structural theorem | True as a fact. **Not a requirement:** AGENTS prefers small exact counterexamples, and 388087 was accepted without one. Using it as a ground would invent a requirement. |
| The open status reflects neglect, not difficulty | **Not established.** Only 3 of 16 citing bodies were read. Lack of engagement fits neglect, or the absence of an obvious method, or the question being peripheral. It cannot ground a verdict. |
| "The first test anyone would run" | **Counterfactual speculation.** The source authors themselves reported only Paley checks (n ≤ 23). |
| A campaign rule makes a side conjecture, computer search or kernel proof alone not significant | **Not textual** (§1). The actual rule is that a closed proof alone does not establish significance, which is correct but neutral. |
| Contrast with 388087: there an all-choices obstruction over a 6,517-leaf tree "carried the substance" | **Misapplied.** The 388087 review explicitly says leaf count and certificate size are not significance evidence; "the consequence for the named conjecture does". Its test is whether known object facts resolve the new property. Here, the known facts do not resolve the minimum distance (existence of non-Paley skew conference matrices, the order-20 SH classification, Theorem 4, and Ball). |
| The AG constructions cannot produce an F₁₉ length-20 code | **Supported** from the secondary description. Additional local point: Harada–Munemasa 2011 (`hm.txt`), which uses exactly the length-n row codes mod p \| k, does not cite AG. This is weak evidence only. |
| Bounded novelty PASS | Supported with the limits in §5. |
| Overall significance FAIL (routine) | **Not upheld.** No explicit construction, bound or reduction is given; the remaining grounds are not AGENTS exclusions (§4). |

## 4. Scientific significance assessment

**Grounds for credit (concrete):**

1. **Exact-scope refutation of a named, published conjecture.** It is Conjecture 1 in IEEE TIT 59(10) (2013) and ISIT 2013, Conjecture 5 in arXiv v1/v2, and open problem 2 in the conclusion. The main assertion itself (MDS) is false. This is not an omitted exception like 337160; the conjecture's core claim fails.
2. **No subsuming reduction.**
   - Ball reframes the conjecture but does not decide it.
   - The classification counts matrix classes but carries no code invariant.
   - The Paley/RS fact covers only the true half.
   - Unlike 325519, I found no generic argument (counting, cardinality or degree) that refutes the universal without examining a specific non-Paley code. A counting attempt fails, because inequivalent matrices could share the single RS code class.
3. **Sharpness at the first nontrivial order.** Combined with §2c, the outcome is a complete picture at p = 19: the conjecture holds for the Paley class and fails for the only other class. This is the "sharpness or classification" feature that the 325519 adjudication found missing there. It is bounded and secondary-sourced, and it is not part of the Lean endpoint.
4. **The obstruction is not a visible local configuration.** Diagnostic `work/sparse_combo_diag.json` (5 s, 1 CPU, 11 MB): over all nonzero F₁₉ combinations of at most 3 rows, the minimum weights are 19/11/14 for **both** W20 and the Paley matrix. So the weight-9 words need at least 4 rows, and the non-Paley/Paley separation cannot be seen in row-pair or row-triple statistics. The Lean word uses 9 rows. This argues against "obvious by inspection". It equally shows the packet offers no conceptual explanation.

**Strongest remaining FAIL case, and why it is not decisive.** The only new mathematical datum is one standard invariant of one textbook object, computed by a textbook algorithm with no new idea. Heuristically, a generic [20,10]₁₉ code is far from MDS: the expected number of rank-deficient 11-sets is in the hundreds, and 180 were observed. So the outcome is the "default" expectation once Ball is known. The conjecture is also peripheral to a Lee-metric paper.

This is a legitimate scientific judgment of *low* significance. But turning it into FAIL needs a rule that the campaign has not written: "finite counterexamples whose only new ingredient is a standard invariant computation on a known object are excluded". Such a rule:
- conflicts with "prefer small exact counterexamples; do not equate shortness with routine adaptation";
- would need consistent application against earlier accepted finite counterexamples.

Heuristic expectation is not proof. The conjecture's authors expected the opposite.

**Conclusion.** The refutation meets the minimum written standard as a novel and substantive finite endpoint, with modest significance. The credit must be described narrowly (see the Recommendation). If root adopts the stricter unwritten rule above, that is a policy decision, not a mathematical finding, and it should be recorded as such and applied prospectively and uniformly.

**Optional suggestion only; this is not new scope.** A structural statement would materially strengthen a paper, but it is not required for this endpoint. Examples:
- non-MDS codes for a non-Paley conference matrix at some infinite family of orders p+1;
- a characterization of conference matrices with GRS row codes.

## 5. Novelty and material body gaps, stated separately

- **AG 2001** (IEEE TIT 47(5), DOI 10.1109/18.930940). Closed; body unread; no lawful copy was found by r1, and I made no retries. Its abstract covers codes from conference matrices, self-duality conditions, examples to length 40, and all weighing matrices of order ≤ 13. Its constructions, per Armario–Frau §1.2, are length-2n [αI | W] and [αI | βI+W] with α, β ≠ 0. For k = p = 19 these require α² ≡ 0, or α² + β² ≡ 0 mod 19 with −1 a non-residue, so they are impossible.
  - **Residual risk:** a remark in the body about length-n row codes when p \| k, or an order-20 F₁₉ table entry.
  - **Exact missing material:** AG §2 (Propositions 2.1–2.2) and its tables.
  - Under the 388087 precedent this is a disclosed limit, not a blocker. If root requires direct clearance, novelty becomes HOLD on exactly this body.
- **GG 2008** (ISIT, DOI 10.1109/ISIT.2008.4595330). Closed; body unread. Its abstract is about existence of self-dual MDS codes (length q+1 for odd q, which is the Paley side). The risk is low; the gap is still disclosed.
- **TIT 2013 journal text.** Glyphs are damaged. Fidelity is limited to the three readable statements plus partial journal text.
- **Other limits:** 13 of the 16 citing works were screened by title only. MathDB state is known only to 04:46 UTC (the inherited 403 was not retried). The openai/math registry head was reused, not re-fetched (§6).

## 6. Remaining limits and conduct

- **Ball** was read in the author-revised preprint, not the JEMS typeset version.
- **Classification:** the SH count and skew normalization come from secondary tables and statements (Araya et al. 2024; Armario–Frau 2013). The primary works (Hanaki et al. 2020; DGS 1971; CRC Handbook) were not read.
- **Minimality** of p = 19 is not established. Uniqueness of conference matrices at orders 4, 6, 8, 12, 14 and 18 is my recollection only, except that orders 4, 8 and 12 have SH count 1 in Table 1. It is not relied on.
- **Registry:** head `4eaee87548250b2682affda7d05d947c05554bae` is taken from recent receipts. This adjudication is not a new discovery investment, so I did not re-fetch it. Root should refresh it before any acceptance. No claim is made about full registry bodies.
- **Lean:** no rebuild by me. I rely on `conference-fidelity-review-r1`: strict replay, leanchecker, and 90 main + 26 control declarations audited.
- **Resources:** one Python diagnostic was run with `taskset -c 0`, `ulimit -v 2 GB` and `timeout 300`; it took 4.84 s wall time and 11 MB RSS. No jobs are left running. There were no network requests, children, git operations, shared or author edits, count changes, publication, uploads, external messages or browser tabs.
