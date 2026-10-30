# Independent adversarial review: MathDB364606

**Verdict: mathematical proof PASS; strict mathematical novelty REJECT.** The full coefficient-sign property is a direct specialization of an explicit published2023 theorem about beta central moments. This does not assert that the2023 paper names or discusses the later Canfield–Helton–Hughes conjecture. It identifies an earlier, stronger mathematical result that already covers its entire scope after an exact generating-function identity. No new-discovery tally credit is recommended.

## Exact source and scope

I independently retrieved the actual [published2026 primary PDF](https://cdm.ucalgary.ca/article/download/80046/58851/277478), extracted it, and visually inspected both p.228's definition and p.241's Conjecture3.2. It defines

    B_r(x)=e^x−Σ_{j=0}^{r−1}x^j/j!,

and conjectures all Taylor coefficients of e^(−x/(r+1))B_r(x) nonnegative for **every integerr≥1**. There is no bounded-degree, asymptotic, or positive-x-only qualifier. The2024 arXiv source labels the corresponding item by subsection3.3.1. The live MathDB post UUID249c8c59-41f0-49a0-9f42-a4a4bdafc971 remainsopen with empty solution/comment lists; that database status does not clear prior-art review.

## Independent algebra audit

Put c_m=[x^(r+m)]F_r and a_m=(r+m)!(r+1)^m c_m. The proposed identities are correct:

    F'_r = r/(r+1)F_r + x^(r−1)e^(−x/(r+1))/(r−1)!,
    a_0=1,
    a_m=r a_(m−1)+(−1)^m C(r+m−1,m), m≥1.

The factorial/index bridge was checked directly: coefficient comparison at degree(r+m−1), followed by multiplication by(r+m−1)!(r+1)^m, gives exactly the displayed recurrence. In particular a_1=r−r=0. For k≥1, eliminating the even intermediate term gives

    a_(2k+1)=r²a_(2k−1)+[2k(r−1)/(2k+1)]C(r+2k−1,2k).

The coefficient uses C(r+2k,2k+1)=[(r+2k)/(2k+1)]C(r+2k−1,2k); its subtraction is exactly2k(r−1)/(2k+1). Thus induction on the odd subsequence, starting at a_1, is valid; each even a_(2k) then adds a strictly positive binomial term. The k=0 odd case must remain the separate basea_1=0; no a_(−1) is used. Coefficients below degreer vanish. Forr=1, oddm vanish and evenm are positive; forr>1, onlym=1 vanishes at or above degreer. These include all degree andr boundaries.

The real-shift classification is also mathematically correct: the degree(r+1) coefficient is[1−λ(r+1)]/(r+1)!, proving necessityλ≤1/(r+1). For sufficiency, multiplyF_r byexp((1/(r+1)−λ)x), whose coefficients are nonnegative. This is a finite Cauchy-product argument coefficient by coefficient.

## Earlier explicit theorem and exact equivalence

Maciej Skorski, *Bernstein-type bounds for beta distribution*, **Modern Stochastics: Theory and Applications10(2)(2023),211–228**, DOI[10.15559/23-VMSTA223](https://doi.org/10.15559/23-VMSTA223), published February13,2023, has an explicit sign result. I retrieved its actual [publisher full body](https://www.vmsta.org/journal/VMSTA/article/265/text) and [published PDF](https://www.vmsta.org/journal/VMSTA/article/265/file/pdf), and read Theorem3/Eq.(7), Corollary3 on p.216, and the recurrence proof in§4.2. Corollary3 states:

> The odd central moments are of the same sign as the value of β−α.

The centered first moment is separatelyzero; the nontrivial odd-order statement concerns orders≥3. The paper's correct recurrence makes that convention immaterial to this review.

Here is the exact bridge, derived independently. Taylor's integral remainder gives

    B_r(x)=x^r/(r−1)! ∫₀¹(1−t)^(r−1)e^(tx)dt.

LetU have the Beta(1,r) densityr(1−t)^(r−1) on[0,1], and letµ=EU=1/(r+1). Then, as entire functions,

    F_r(x)=x^r/r! E exp(x(U−µ)),
    [x^(r+m)]F_r(x)=E[(U−µ)^m]/(r!m!), m≥0.

No coefficient sign is changed by this identity. The factorx^r handles every coefficient belowr. Even central moments are nonnegative;µ_0=1 andµ_1=0. Skorski's Corollary3 gives all remaining odd signs forα=1,β=r≥1. Therefore its explicit theorem covers **every coefficient for every source r**, rather than supplying only an ingredient or a bounded case.

Theorem3 itself independently confirms the reduction. WithM_d=E[(U−µ)^d], its recurrence specializes to

    M_d=[(d−1)(r−1)/((r+1)(r+d))]M_(d−1)
        +[(d−1)r/((r+1)²(r+d))]M_(d−2), d≥2.

Both coefficients are nonnegative, and the second is positive. HenceM_d≥0 by induction from1,0, with exactly the proposed strictness pattern. This recurrence can also be checked by integrating the derivative of t(1−t) times the beta density against(t−µ)^(d−1); it is not dependent on a possibly misread hypergeometric convention.

The optimal shift does not escape this prior result: it is the same known centered-moment sign statement multiplied by a nonnegative exponential, with necessity from the first shifted momentEU−λ. No independent new mathematical phenomenon has been identified in that classification.

## Formal-review limit and artifact binding

The worker was still building the coefficient recurrence bridge when this novelty exclusion was found. I did not certify an unfinished Lean module as a complete formal outcome or repeat its build. Snapshot hashes at this review:

- Worker proof note `new-screen/STIRLING-PROOF-CANDIDATE.md`: b988557c37eea5698af2250d640045788fd0c30679c870405fcf315b6b0aa26e.
- Worker in-progress `formal/StirlingPositivity.lean`:9a6712d11da50fbab9c48fb3b8c8103e1497df6f5d67a661a9fa3e02a221df59. It was not frozen and may evolve.
- Independently fetched2026 PDF:be210e518e45f1dc6e9aa7dbf792046e2d83fdd33f09a327e7a95bcb382829dd.
- Independently fetched Skorski2023 PDF:744a906e560bc30e58e45f398d363170c170424183571d8eb941eb7ae2467eb9.
- Skorski publisher HTML:df57544e77d08e526b16a24dd2eeaecab95a23fd65417c30e8a13858ea344eaa.
- Live MathDB snapshot:370d90efd2dc76543a11a7debf45a401853a01c6ebb9af83a69e9e094fd9e2dc.

All independent source files and rendered source pages are retained under this review's `sources/`. The recurrence proof remains useful as a new formalization or an independent proof of the conjecture's literal statement, with Skorski's prior theorem prominently credited. It should not be counted toward the user's strictly new mathematical-discovery objective.
