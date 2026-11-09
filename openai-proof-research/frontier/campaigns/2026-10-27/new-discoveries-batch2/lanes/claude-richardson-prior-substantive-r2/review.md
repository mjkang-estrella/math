# Independent specialist prior/substantive gate: Richardson Conjecture 5.1

Reviewer: Claude Opus 5.5 (high effort, standard speed), third slot, solo, no children.
Administrative snapshot: 9 additional / 39 total / next 40. This review grants no credit and changes no count. Root alone accepts, counts and stages. Root's involvement in the route carries no authority in this review.

## Decision

**Recommendation to root: EXCLUDE as a routine classical corollary. Do not INVEST (no Lean, no manuscript).**

| Gate | Verdict |
|---|---|
| SOURCE | PASS (inherited; FQ PDF hash reconfirmed) |
| MATH (Sol PROOF.md) | PASS; no error found. A much shorter independent proof is given below. |
| SUBSTANTIVE | **FAIL under the campaign standard.** The complete bridge is exhibited in §2. |
| NOVELTY | No earlier explicit printed statement of the full criterion was located in bounded actual-body screens. No prior publication is asserted. |
| FORMAL | Not investigated; no investment recommended |

The exclusion does not rest on shortness, on the conjecture label, or on a no-match search. It rests on two concrete findings. Neither appears in either predecessor document (frozen PROOF.md/discovery.md, frozen review.md).

1. **Factual correction (same-object prior).** Berg, *Fibonacci numbers and orthogonal polynomials*, Section 4, treats exactly Richardson's reciprocal-binomial matrix. It is not only the 1/(α+i+j) family. Berg proves the kernel formula and that all denominators divide r.
2. **Complete short classical bridge.** Start from Berg's kernel. The textbook Christoffel–Darboux (CD) formula plus the identity (2n−1)² − 4n(n−1) = 1 give the full iff in a few lines. They also give the exact common-denominator law r/gcd(r, n(n−1)), which predecessor r1 had observed but left unproved. The arbitrary-shift linearization, the shifted telescoping and the carry/valuation split are all unnecessary.

## 1. Same-object prior: Berg Section 4 (actual body read)

Body: https://arxiv.org/pdf/math/0609283, SHA256 `2813148b…180b8c`. This is the inherited lawful copy, and its hash still matches the receipt (reference-bindings-supplement.json). I re-extracted the text myself into derived/berg-own-extract.txt. The PDF contains two embedded versions: the original preprint at extracted lines ~1–930, and v2 with "Added June 2007" at ~940–1770. The statements below occur in both (lines 838–894 and 1635–1697).

Exact content, notation α ∈ N:
- Eq. (39): the probability measure α(1−x)^(α−1) on ]0,1[ has moments s_n = 1/C(α+n, n). The orthonormal polynomials are sqrt((α+2n)/α)·r_n^(α)(1−x).
- Eq. (40): K_n(x,y) = Σ_{k=0}^n ((α+2k)/α) r_k^(α)(1−x) r_k^(α)(1−y). "The coefficient to x^i y^j in αK_n(x,y) is an integer when α ∈ N."
- **Theorem 4.2.** Let α ∈ N. The inverse of the matrix (1/(α·C(α+i+j, α)))_{0≤i,j≤n} has integer entries.
- Displayed after the theorem: r_n^(α)(1−x) = Σ_k (−1)^(n−k) C(n,k) C(α+n+k−1, k) x^k. The entries of the inverse of (41) are
  (−1)^(i+j) Σ_{k=max(i,j)}^{n} (α+2k) C(k,i) C(k,j) C(α+k+i−1, i) C(α+k+j−1, j). "This formula holds of course for any α > 0."
- For α = 2: "Theorem 4.2 can be sharpened: the inverse of the matrix 1/C(2+i+j, 2) has integer coefficients. This result is also given in [Richardson]."
- Section 4 also gives the leading coefficients and norms used below: Dn−1/Dn and (37).

**Substitution.** Take α = r and Berg's n = (our n) − 1. Then (41) = R/r with R_ij = 1/C(i+j+r, r). The displayed entry is (−1)^(i+j)·N[i,j], where P_i(k) = C(k,i)C(k+r+i−1,i) and

    N[i,j] = Σ_{k<n} (2k+r) P_i(k) P_j(k),    (R^{-1})_{ij} = (−1)^{i+j} N[i,j] / r.

This is literally PROOF.md eq. (1). So PROOF.md §1 and the "denominators divide r" statement are Berg's same-object theorem, not merely a specialization of his generic Theorem 2.1.

The predecessors' statement that "Section 4 concerns 1/(alpha+i+j)… a different family" is incomplete. Section 4 contains both Theorem 4.1 (Hilbert-type) and Theorem 4.2 (exactly this matrix).

**Missing hypothesis relative to Conj 5.1.** Berg proves only r·R^{-1} ∈ Z^{n×n}, plus the α=2 sharpening. That is Richardson's own 2001 observation ("when the entries are not integers, the denominators are divisors of r"), not the iff. Berg does not mention Conjecture 5.1.

My checker verifies Berg's displayed formula against exact rational inverses on 35,904 entries.

## 2. Complete classical bridge to the full iff (independent proof)

Fix integers n ≥ 1 and r ≥ 1. Let Q_k(x) = Σ_i (−1)^i P_i(k) x^i. In Berg's notation Q_k(x) = (−1)^k r_k^(r)(1−x). These polynomials have integer coefficients and leading coefficient L_k = (−1)^k C(2k+r−1, k). They are orthogonal for ⟨f,g⟩ = ∫_0^1 f g (1−x)^(r−1) dx with h_k = ⟨Q_k,Q_k⟩ = 1/(2k+r) (Berg §4; also PROOF.md §1).

**(a) CD formula.** This is the textbook theorem for any orthogonal polynomial sequence of exact degrees: Szegő, *Orthogonal Polynomials*, Thm 3.2.2; Chihara 1978, Thm I.4.5, which is Berg's own reference. Those two book bodies were not re-read in this lane; the standard statement is used.

    Σ_{k<n} Q_k(x)Q_k(y)/h_k = (L_{n−1}/(L_n h_{n−1})) · D(x,y),
    D(x,y) = (Q_n(x)Q_{n−1}(y) − Q_{n−1}(x)Q_n(y))/(x−y).

D lies in Z[x,y], because each (x^s y^t − x^t y^s)/(x−y) is an integer polynomial. The leading-coefficient ratio is C(2n+r−3,n−1)/C(2n+r−1,n) = n(n+r−1)/((2n+r−1)(2n+r−2)). Hence the constant is −n(n+r−1)/(2n+r−1). Comparing coefficients of x^i y^j:

    (2n+r−1) · (−1)^{i+j} N[i,j] = −n(n+r−1) · D_{ij},  D_{ij} ∈ Z.          (CD)

This holds for every n ≥ 1, including n = 1, where D = −(r+1) and N = r. It is verified exactly on 35,904 coefficient entries (check-results.json).

**(b) Arithmetic identity.** (2n−1)² − 4n(n−1) = 1, so gcd(n(n−1), 2n−1) = 1.

**(c) Sufficiency.** Suppose r | n(n−1).
- Then r | n(n−1) + nr = n(n+r−1), so r | (2n+r−1)·N[i,j] by (CD).
- Any common divisor d of r and 2n+r−1 divides 2n−1 and n(n−1), so d = 1 by (b).
- Hence r | N[i,j] and R^{-1} is integral.

**(d) Necessity.** N[0,0] = Σ_{k<n}(2k+r) = n(n+r−1), so (R^{-1})_{00} = n + n(n−1)/r.

**(e) Exact denominator law (bonus, same lines).** Let d = gcd(r, n(n−1)).
- The argument in (c) with d in place of r gives d | N[i,j] for all i, j.
- gcd(r, N[0,0]) = gcd(r, n(n+r−1)) = d.
- Hence gcd(r, all N_ij) = d, and the lcm of the denominators of R^{-1} is exactly r/gcd(r, n(n−1)).

This is predecessor r1's observed but unproved law. It is verified on 384 (n, r) cases. It deserves no separate credit.

**Assessment.** The full source endpoint, and even the stronger denominator law, follows from:
- a published same-object kernel (Berg Thm 4.2 and its displayed formula, 2006/2011);
- a textbook theorem (CD) with constants read off Berg §4;
- a one-line gcd identity.

No new identity, estimate or mechanism remains. This is the campaign's "routine corollary" category. It sits closer to the excluded Bessel-ratio, silicosis and Eruguz cases than to any accepted outcome, and it is shorter than several of them. Sol's linearization/telescoping/Kummer route is correct but is not needed. Its length overstated the substantive margin.

This argument was found by this reviewer, not located in print. It is the decisive classical bridge, not a prior publication. A specialist who has Berg §4 in hand would be expected to apply CD; Berg applies exactly that kernel–CD viewpoint to Hilbert matrices in the same section.

## 3. Arbitrary-shift linearization question (now non-decisive)

The assignment asked whether a prior body states P_iP_j = Σ_l C(l,i)C(l,j)C(r+i+j−1,i+j−l)P_l, or the shifted weighted sum, for arbitrary shift.

- No body read in this lane states the all-shift integral formula.
- The predecessors' Guo–Zeng 1101.0983 reading (shift 1 only) was not re-read here. My decision does not depend on it.
- These identities are Pfaff–Saalschütz/Gosper-type classical evaluations. Their prior-print status no longer affects the substantive decision, because §2 bypasses them entirely.

No arbitrary-shift linearization result should be credited separately.

## 4. Actual bodies read in this lane, with exact relevance

All retrieval was guarded, single-attempt, and logged in http.jsonl (UTC, URL, status, SHA256).

- **Richardson, FQ 39(3) 2001**, §5–6. Cached text; PDF SHA `09eebfb0…3d4e` matches the inherited receipt.
  - Conj 5.1 is quoted in the inherited review.
  - Richardson's text: "when the entries are not integers, the denominators are divisors of r" (an observation, unproved there).
  - Thm 5.1 (r=2, parity) and Thm 5.3 (c_k = C(k+3,3), mod-3 argument) are partial. Thm 5.2 is an explicit WZ-verified inverse.
  - Conj 6.1 (Fibonomial) is separate.
- **Berg, arXiv math/0609283v2** (v1 11 Sep 2006, v2 5 Aug 2010; journal Arab J. Math. Sci. 17 (2011) 75–88). §1 and §4 in full, as in §1 above.
- **Richardson, arXiv 2005.08939v3**, *Catalan Numbers and Jacobi Polynomials* (v1 18 May, v2 19 Jul, v3 25 Aug 2020). SHA `935e56d2…0022191`. Read: intro, §2, §7 Thms 7.1–7.2, §8, references.
  - The author cites Berg Thm 4.2 for "bₙ = α·C(n+α, α), α natural". That is the scaled version only.
  - For rational parameters q/p he proves (1/q)G^{-1} integral (Thm 7.2), and integrality only for q = ±1, ±2 (Thm 7.1).
  - No mention of Conj 5.1 status. This is chronology evidence that the conjecture's author did not record a resolution through 2020. It is evidence about the record, not about routineness.
- **Richardson, arXiv 1405.6315v1** (24 May 2014), *The Reciprocal Pascal Matrix*. Entries 1/C(i+j,i), a different object. Integrality is shown via factorizations; Conj 5.1 is not mentioned.
- **Cigler, arXiv 1703.00763v3** (v1 2 Mar, v2 7 Mar, v3 24 May 2017). Hilbert-matrix inverse via orthogonal polynomials (Thm 2.1, r=1 only) and harmonic-number Hankel determinants. No reciprocal-binomial shift.
- **Andersen–Berg, arXiv math/0703546v1** (19 Mar 2007). Quantum Hilbert 1/[α+i+j]_q inverse (Thm 2.1) and Filbert specialization (Thm 3.1). No reciprocal q-binomial integrality criterion.
- **Kılıç–Prodinger, FQ 48 (2010) 29–33**, https://www.fq.math.ca/Papers1/48-1/Kilic_Prodinger.pdf. Entries 1/F_{i+j+r} (Fibonacci), LU/inverse via q-Zeilberger. Not this object.
- **Cigler–Tyson, arXiv 1807.08330v2** (29 Oct 2018). Root pointer from completed r216; hash-bound before reading, SHA `3e5a6d56…6fa6e6`, matching r216's receipt.
  - Content: determinants of Hankel matrices of C(2n+r, n). Not reciprocals, no inverse-integrality, and no Richardson/Berg/CD citation.
  - Its three references are determinant evaluations: Cigler 1801.05608; Cigler–Krattenthaler 2011; Eğecioğlu–Redmond–Ryavec 2010.
  - Lemma 7.3 inverts an unrelated matrix.
  - Distinct from Conj 5.1, as root noted; not used for or against exclusion.

## 5. Citer and registry coverage (bounded)

- **OpenAlex citers** of the three Richardson records (W1557337690, W4407277396, W4394643473): 24 works. With Berg's two records: 42 works, abstracts decoded.
  - They are Kılıç–Prodinger-family Fibonacci/Lilbert/q-Pilbert/super-Catalan LU papers, OP/moment theory, and noise.
  - None claims a reciprocal-binomial integrality criterion.
- **OpenAlex citers of Richardson 2020:** 0.
- **Semantic Scholar:** Berg citers (35) were listed. A Richardson arXiv-id lookup returned 404, and a later search returned **429**. The host was stopped for this lane with no retry.
- **arXiv metadata searches** ("Filbert"; reciprocals/binomial/Hankel/inverse; "Pilbert"; Hankel/reciprocals/integer inverse; Richardson author): only Richardson 1999/2014/2020 and Andersen–Berg are mathematically relevant. "Filbert" hits are otherwise an author surname.
- **zbMATH Open:** the Filbert search lists Richardson Zbl 0994.11011 and the Kılıç–Prodinger family; contents are license-restricted. The `ci:0994.11011` cited-by query returned "No results found" (404 body, not a denial).
- **OEIS** "Filbert": 2 hits (A010048, A062381), Fibonacci only.
- **MathOverflow / Math.SE** API "Filbert matrix": 0 items.
- **OpenAlex full-text** "reciprocals of binomial coefficients": 110 titles, all series/sum identities. Titles only, not bodies.

**Unread (not essential to the EXCLUDE recommendation):**
- Berg AJMS 2011 VoR and Andersen–Berg JCAM VoR (ScienceDirect: inherited denial, not attempted).
- Berg's NORMAT 2006 Danish survey (covers α=1,2 per Berg's own statement).
- Kılıç–Prodinger-family journal bodies, Prodinger super-Catalan bodies, and *The inverse Filbert matrix* (Afrika Mat. 2014).
- Szegő/Chihara book bodies (textbook CD).
- Any current public proof-registry head: GitHub API/raw/codeload routes are inherited denials and were not attempted. There is no authenticated registry result, and none is claimed clean.

None of these could convert the exclusion into credit. A located prior proof would only add a second exclusion ground.

## 6. Actionable recommendation

**EXCLUDE**, with this suggested ledger wording:

> Berg (arXiv 2006; AJMS 2011) §4 Thm 4.2 and its displayed formula give the same-object kernel r·R^{-1} = ((−1)^{i+j}N_ij), N integral. The textbook Christoffel–Darboux formula gives (2n+r−1)N = ∓n(n+r−1)D with D integral, and (2n−1)² − 4n(n−1) = 1 makes 2n+r−1 a unit mod r whenever r | n(n−1). The corner gives necessity, and the same lines give the exact denominator r/gcd(r, n(n−1)). This is a routine classical corollary. No earlier explicit printed proof of Conj 5.1 is asserted.

Further:
- Sol's linearization/carry proof: retain as correct; no credit.
- Exact denominator law, shifted linearization, telescoping and the Fibonomial analogue: no separate credit from this route.
- No essential unread body blocks the recommendation.
- If root nevertheless considers acceptance, the minimum missing items are (i) a lawful current public proof-registry check and (ii) the Berg VoR via a non-denied lawful route. Neither answers the routine objection in §2.

## 7. Validation and custody

**checker.py** (guarded; n ≤ 16, r ≤ 24, exact Fractions/integers; check-results.json):
- 35,904 Berg-formula entries;
- 35,904 CD-identity entries;
- 16 gcd identities;
- 384 iff cases (130 integral);
- 384 exact-denominator-law cases.

These are finite error-detection checks; the universal argument is §2.

**Custody:**
- Scientific inputs were copied and hash-bound before reading (input-bindings.json).
- Admin NEXT/ledger/context/AGENTS are snapshots only.
- Cached predecessor Berg/FQ texts were bound *after* reading (deviation in FAILURES.md). Their PDFs match inherited receipts.
- r216 references were bound before reading.
- The manifest excludes manifest.json and verification-receipt.json and is verified in a separate guarded run.

No Lean, manuscript, git, shared edits, browser, MathDB edits, external messages, posts or uploads. No parked merge-tree or capped interval was reopened.
