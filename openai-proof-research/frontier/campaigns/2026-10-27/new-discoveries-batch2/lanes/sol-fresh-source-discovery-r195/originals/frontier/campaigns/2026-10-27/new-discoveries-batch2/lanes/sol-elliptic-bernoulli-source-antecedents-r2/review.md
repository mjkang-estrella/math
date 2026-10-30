# Source and same-object antecedent review, r2

2026-10-29 UTC. SOLO. Credit 0. **Source: HOLD. Bounded substantive eligibility: FAIL (recommend routine-corollary exclusion on newly authenticated published product identity).** This is a recommendation to root, not adoption, acceptance, a formal certificate, or a count change. Counts remain 5/30 additional and 35/60 total. No Lean or manuscript investment.

The original ordinary all-order proof remains PASS on the literal arXiv definition. I read PROOF.md and independent review.md completely, the root adoption, ancestor/batch AGENTS.md, ledger and prior context. Root's prior decision correctly rejected an exclusion based only on the sigma PDE. The new evidence below supplies the specific published product evaluation previously missing. I do not assert that a prior author announced a proof of Grosset–Veselov Conjecture 2.

## 1. Published 2006 source authentication: HOLD

Target: Grosset–Veselov, IMRN 2006, article 62120, DOI 10.1155/IMRN/2006/62120. Live Crossref JSON authenticates this bibliographic identity and marks its Oxford PDF link content-version=vor. It does not supply the body. Oxford and the old institutional handle were NOT retried. New lawful routes:

- Author's current Loughborough staff page: HTTP200, links to the institutional publication list, no new target PDF link found in that page.
- Author's Landau Institute publication list: HTTP200; the target entry links DOI and arXiv, without a separate VoR download. Saved HTML includes the literal entry.
- EMIS journal-directory route: redirected to zbmath serials, HTTP403; stopped.
- Former publisher's public download archive, https://downloads.hindawi.com/journals/imrn/2006/062120.pdf: HTTP403 HTML challenge/error, stopped; saved bytes are **not a PDF/source body**. No altered path, headers, challenge solving or follow-up on that blocked route.
- Figshare public API rechecked: article9383633 still advertises only 05-43.pdf, file16995383, published_date 2005-11-10T11:12:43Z. Own copy of the previously downloaded PDF hashes to 94b33c446913b2cc227a9530ee300357d07072888602f8ebd451d70ab1c2baa6. This is preprint evidence. It predates the recorded March2006 revision/acceptance and has no authenticated VoR status.

Therefore I cannot state the exact published Conjecture 2, equation (21), or revisions/hypotheses match arXiv. The original-source publication gate remains HOLD, even though the antecedent gate now has concrete positive evidence. No abstract, Crossref metadata, or matching preprint is promoted to a read published body.

For the exact accessible object I copied the frozen arXiv PDF/text and rendered/read pp11 and17. Equation (21) is B_(2m)=1/2 integral_gamma (d^(m-1)wp/dz^(m-1))^2 dz. Conjecture2 says B_(2m)=(-1)^(m-1)(Ahat^(m)(g2,g3)*omega-Bhat^(m)(g2,g3)*eta), with positive rational polynomial coefficients. It specifies no numerical positivity of invariants. The curve is y²=4x³-g2*x-g3; cycle periods are 2omega=integral dz and -2eta=integral wp dz. The analytic proof applies to nonsingular curves g2³!=27g3² and compact cycles avoiding infinity, and the claim is about universal polynomial coefficients. The preprint's discriminant specialization is a separate limiting statement. Its printed B2 discrepancy remains uncredited and cannot be used as a source refutation. The m1 eta polynomial has empty support. Conjecture1 about all lambda coefficients is outside this review.

## 2. Authenticated published same-product antecedent

**Song He and Yuan Sun, “Correlation functions of CFTs on a torus with a T Tbar deformation”, Physical Review D 102, 026023 (published 28 July2020), DOI10.1103/PhysRevD.102.026023.** Actual publisher PDF downloaded200, 359611bytes, SHA256 **5a1429e2a76dcad32178f6d2288a9f1d47dbab432669acf652167c4a7e11cb6f**. First page identifies journal, DOI, publication/acceptance dates and APS publication. Relevant pages026023-18 and026023-19 were rendered and visually read, including Appendix D.1, displays D20–D27. URL: https://journals.aps.org/prd/pdf/10.1103/PhysRevD.102.026023 . This is an authentic published body, not a snippet or a citation to an unread general method.

D21–D23 explicitly evaluate the same product. In their notation P=wp and zeta'=-P. If d=a-b, they give

    P(z-a)P(z-b)
      = C + P'(d)(zeta(z-a)-zeta(z-b))
          + P(d)(P(z-a)+P(z-b)),
    C = P(a)P(b)+P'(d)(zeta(a)-zeta(b))
                         -P(d)(P(a)+P(b)).

D26 integrates it over torus area, and D27 differentiates in the displacement twice. I do **not** identify that area integral with the candidate's cycle integral. The stronger useful antecedent is the pointwise D21–D23, which may be integrated on a cycle directly.

Crucial version warning: the separately retrieved arXiv PDF2004.07486 (269681bytes, SHA ce43bfa07a134feb70597354b08ccf54986653c2f964e23a690a04679fe150e0) has a **minus** sign in its equations128–129 where the published D22–D23 have **plus**. The minus sign fails the residue at z=a, whose value must be P'(a-b). The published signs are correct and visually verified. Thus relying on the preprint alone would have given a false bridge. The published statement, not the preprint typo, is the antecedent used here.

### Literal substitutions and every scope bridge

1. Fix a nonsingular lattice and take nonlattice t near0. In D21–D23 put a=epsilon, b=epsilon-t, and take epsilon to0. This is an ordinary meromorphic identity limit; its final right side is regular in epsilon. Set p=P. Expansions

       p(e)=e^-2+O(e²), p(e-t)=p(t)-e p'(t)+e² p''(t)/2+O(e³),
       zeta(e)=e^-1+O(e³), zeta(e-t)=-zeta(t)-e p(t)+O(e²)

   cancel the e^-2 and e^-1 terms in C. The constant becomes p''(t)/2-p(t)²+p'(t)zeta(t). Using p''=6p²-g2/2 gives C=2p(t)²-g2/4+p'(t)zeta(t). Hence the published D21–D23 become exactly PROOF.md(C), including its constant and sign. bridge_check.py independently checks this limit symbolically and diagnoses the preprint sign failure; this is not numerical novelty evidence.

2. Integrate this pointwise identity on any compact period-cycle representative avoiding poles, for t in a uniform small disk. The period of p(z+t) equals that of p(z): differentiate under the contour and integrate the exact differential d(p(z+t)); endpoints agree by periodicity. Both periods are -2eta. If J(t)=integral(zeta(z)-zeta(z+t))dz then J(0)=0 and J'(t)=-2eta. Thus J=-2eta*t. No claim that zeta itself is periodic, or that a contour can be shifted across a pole, is needed. With integral dz=2omega, division by2 gives

       (1/2) integral p(z)p(z+t)dz
        = omega*(2p(t)²-g2/4+p'(t)zeta(t))
                           -eta*(2p(t)+t p'(t)).                    (*)

3. Use the already body-read Buchstaber–Bunkova1204.3784 §8.4 Theorem37 (own copied PDF, p15 rendered/read). Its Q2 sigma=0 in this exact g2,g3 normalization implies, by taking a logarithm and applying -d_t²,

       delta p = 2p²+zeta*p'-g2/3,
       delta=6g3*d_g2+(g2²/3)*d_g3.

   No contour or period is differentiated in invariant space. Substitution into (*) gives precisely the requested full period-correlation identity

       (1/2) integral p(z)p(z+t)dz
        = omega*(delta p(t)+g2/12)-eta*(2p(t)+t p'(t)).       (**)

   The heat theorem alone did not supply (*); the newly authenticated published D21–D23 do. This is the change in evidence from r1.

4. The left side is analytic near t0 because the contour is compact and avoids the translated poles. Its t^(2m-2) coefficient is integral p*p^(2m-2)/(2(2m-2)!). Integrating by parts m-1 times gives (-1)^(m-1)B_(2m)/(2m-2)!, with no boundary terms. On the right of (**) the coefficient is omega*delta c_m -eta*2m*c_m for p=t^-2+sum_(m>=2)c_m t^(2m-2). Therefore for every integer m>=2,

       Ahat=(2m-2)! delta c_m,
       Bhat=2m(2m-2)! c_m.

   This recovers both coefficients simultaneously, without a finite truncation restriction. The constant term is g2*omega/12 (m1). Applying the same identity to both basis cycles and using the nonzero Legendre determinant uniquely identifies the coefficient polynomials. Additivity handles all cycles; zero residues of the even elliptic differentials handle loops around infinity.

5. He–Sun use periods1,tau with Im(tau)>0; this does not restrict the result to real invariants or real cycles. For any lattice choose ordered basis 2omega1,2omega2 and rescale z=(2omega1)u, tau=omega2/omega1. wp scales by (2omega1)^-2, zeta by (2omega1)^-1, g2 by (2omega1)^-4 and g3 by (2omega1)^-6. Each term of D21 has degree -4 under this scaling. It is therefore a universal pointwise identity for arbitrary nonsingular lattices; integrating it works for either cycle, regardless of the area-integration convention in the physics application. D21–D23 are identities of ordinary elliptic functions and impose no CFT, state, charge, positivity or real-lattice hypothesis on that algebraic identity.

6. Full positivity now uses exactly the source's already printed positive Laurent recurrence: c2=g2/20,c3=g3/28 and c_r=3/((2r+1)(r-3))*sum_(s=2)^(r-2)c_s*c_(r-s), r>=4. Induction gives positive rational coefficients on full weight2a+3b=r support. Delta maps g2^a*g3^b to 6a*g2^(a-1)*g3^(b+1)+(b/3)*g2^(a+2)*g3^(b-1). For a target of weight m+1, use preimage(a+1,b-1) if b>=1, or(a-2,1) if b0; the latter has a>=2. All multipliers are positive. No extra conjectural coefficient bridge remains.

This is a complete ordinary reduction to actual published same-object product evaluation plus the read heat theorem and source recurrence. No claim of an earlier printed full endpoint is required for the campaign's routine-corollary exclusion.

## 3. Eligibility calibration and strongest contrary case

Recommendation **FAIL**, limited to the candidate's full arXiv-Definition21/Conjecture2 result. The exact product to which its entire analytic bridge applies is now explicitly evaluated in a 2020 published body, before this campaign. The remaining operations are a regular displacement limit, termwise cycle integration with elementary quasiperiod shifts, substitution of the read heat theorem, Taylor extraction/IBP, and the source's positivity induction. No new choice of elliptic object or unsolved evaluation is left. Every classical tool is uncredited.

Strongest contrary case: He–Sun do not name elliptic Bernoulli periods or the conjecture, their final integration is two-dimensional, and converting to two cycle coefficients with an invariant derivative is useful cross-literature assembly. Such an assembly could justify a mathematical note. The original source's age and conjecture status could suggest that the connection was missed. Those points are preserved; they are not disproved by brevity. My exclusion judgment rests on the specific D21–D23 evaluation and the explicit complete conversion above, rather than generic-tool reuse or shortness.

I read root-gamma-level-formal-r1/INVESTMENT-DECISION-R2.md, root-hoggatt-r1/ROOT-DECISION.md and astra-an-djokovic-preliminary-review-r1/corollary-bridge.md. Gamma preserved a concrete object-to-perspective identification where no inspected theorem evaluated the Gamma curve. Hoggatt excluded a source induction once the exact separated kernel was supplied. An–Djokovic excluded a complete endpoint specialization of an actual monomial evaluation even though the final endpoint had not previously been printed. Here the new actual same-product evaluation removes precisely the reason r1 favored gamma-style preservation. This remains a root eligibility judgment to adjudicate, not a self-executing rejection of the candidate.

## 4. Other targeted bodies and limits

The live modular/Rankin-Cohen search led to Dumas–Martin–Royer, Differential algebras of quasi-Jacobi forms of index zero, author-hosted PDF. Read §3.7 definition26, proposition28 and equation45 on pp17–18: these give an Oberdieck/modular derivative identity for wp, not a period-product evaluation. The fetched English body labels itself an automatic translation from the author's French version; I do not certify its published-version status or use it as a decisive dependency.

Downing et al., JHEP06(2026)114, published10June2026, was obtained through the publisher-supplied SCOAP3 record and its advertised fulltext file. Inspected appendixF, especially F.1–F.2 (printed35–36; PDF pp36–37), and the corresponding arXiv text: multiplicative-coordinate single-function and multi-integrals, including derivative-Eisenstein expressions. No independent full candidate subsumption is claimed from those inspected formulas. Not necessary once the older exact He–Sun decomposition is authenticated. No exhaustive paper read claimed.

An ETH public bitstream for a Weierstrass-integrals appendix returned429; stopped and did not retry. MPI challenge route, truncated handbook and old Oxford challenge were not retried. No assertion of reading Hermite/Halphen originals, complete nineteenth-century tables, or all Rankin-Cohen/VOA literature. The bounded search is now positive on one concrete equivalent product, not a universal absence or priority certification.

No registry updates were needed for this classical-antecedent determination. Preserve r1 chronology and its dev31c2fcf8d598e1a26f6ea185f08b50a47ac9dd54 3commit/217file delta from6e842c9..., with the other four heads unchanged as recorded there. This report makes no fresh whole-dev completeness claim. Pinned OpenAI theorems are accepted as true; no upstream audit.

## 5. Integrity and handback

All49 original candidate files matched root-elliptic-bernoulli-handback-r1/review-freeze.json before work. Own copies only were used for extraction/rendering/checking. After work all49 match again (freeze-after.json). The original candidate and adopted proof-review artifacts were not edited. No git, children, sibling polling, contacts, posting, accounts or browser tabs. New files are confined to this assigned lane.

provenance.json records exact live URLs, UTC access dates, statuses, hashes, copies and inspected ranges. http.json saves failures as well as successes; filenames ending.pdf for403/429 bodies are explicitly not genuine sources. Finite resource controls for the symbolic sign/limit check:512MiB hard AS,20CPU seconds,25s alarm,30s external timeout, BLAS/OMP/MKL1. PDF rendering/extraction:512MiB AS,30CPU seconds, thread counts1. No large proof checker rerun or finite data presented as an all-order proof.

Hand back source HOLD and bounded eligibility FAIL separately. Preserve ordinary proof PASS, credit0, and no formal/manuscript/acceptance work. The source question cannot be certified as the actual published2006 claim until its body is read, even if root adopts the exclusion of the accessible candidate result.
