# MathDB 352905: ordinary counterexample; no Lean endpoint

Status: CANDIDATE / HOLD. Zero accepted credit. Root decides significance and acceptance. The literal chromatic-symmetric-function semantics have NOT been formalized. Journal Section 3 remains unread beyond the accessible preview. No novelty clearance is claimed.

## Exact source and object

Wang and Wang, arXiv:2112.06619v1 (the only arXiv version listed on the retrieved abstract page), Conjecture 3.5: if b is even and b is not 2 modulo 3, S(b²+b,b,1) is e-positive. Its surrounding sentence reports checks only for b = 4 and 6. The spider S(a,b,c) has legs of edge lengths a,b,c, hence a+b+c+1 vertices. We take b = 24, a = 600; n = 626. All hypotheses hold: 24 is even, 24 ≡ 0 mod 3, and 600 ≥ 24 ≥ 2. This is not a convention or endpoint counterexample.

## Ordinary proof relative to the printed standard CSF identities

Write P_n for a path on n vertices and X_G for its chromatic symmetric function. Source Lemma 2.10 at c = 1 gives

    X_S(600,24,1) = X_P626 + e_1 X_P625 − X_P25 X_P601.

Consider the elementary-basis coefficient of e_6 e_5^124, a partition of 6 + 5·124 = 626. The e_1 term contributes zero. The path generating series is

    Σ_{n≥0} X_Pn z^n = (Σ_{j≥0} e_j z^j) / (1 − Σ_{j≥1} (j−1)e_j z^j), e_0=1.

This is equivalent to the source's cited Wolfe coefficient formula, Proposition 2.5. To extract the chosen coefficient, set e_5 = x, e_6 = y and all other positive-degree elementary generators to zero. The series becomes

    (1+xz^5+yz^6)/(1−4xz^5−5yz^6).

For t ≥ 1, extraction gives

    [x^t] X_P(5t) = 5·4^(t−1),
    [x^t y] X_P(5t+6) = (25t+24)·4^(t−1).

Indeed, the latter coefficient comes from the constant numerator, xz^5 numerator and yz^6 numerator with contributions 5(t+1)4^t, 5t4^(t−1), and 4^t. Their sum is (25t+24)4^(t−1).

Thus [e_6e_5^124]X_P626 = 781·4^124. The only subpartition of (6,5^124) of weight 25 is (5^5), since 6+5j≠25 for every integer j. The product term consequently has coefficient

    [e_5^5]X_P25 · [e_6e_5^119]X_P601
      = (5·4^4)(2999·4^118) = 14995·4^122.

Subtracting gives

    [e_6e_5^124] X_S(600,24,1) = −2499·4^122 < 0.

Hence S(600,24,1) is not e-positive. This refutes the arXiv statement of Conjecture 3.5.

## Why the search first failed at b = 24

The tested admissible b values before 24 have b+1 prime. In general let b+1=ds with d,s≥2, and put t=ds²−1. The same coefficient for partition (d+1,d^t) has value

    (1−d³s(s−1)) (d−1)^(t−2),

provided the weight b+1 subpartition is only d^s (automatic for this support), and t≥2. It is negative. The exact reserved endpoint needs only d=s=5. This observation remains within the assigned spider family; it is not a second credited result.

## Independent verification and limits

`scripts/spiders.py` searches exact rational Wolfe coefficients for specified two-size-support partitions, b = 4,6,10,12,16,18,22,24,28,30; outputs preserve all discovered negative coefficients. `scripts/verify_spider.py` independently uses the bivariate generating-series recurrence P[t,u]=4P[t−1,u]+5P[t,u−1]+numerator[t,u], without the factorial expression. It verifies the three path coefficients and −2499·4^122 exactly. Both outputs are retained.

The source's neighbouring Theorem 3.3 gives only the necessary alternative a≤b²−1 or a=b²+b, leaving the exceptional case open; it does not itself state this negative coefficient. Nonetheless the proof is a short extraction from two printed identities, and root must assess whether it is a routine source specialization under the campaign's unusually strict credit policy. No independent reviewer has adjudicated it.

Bounded title, conjecture, exact-object and coefficient searches found no exact printed counterpart. A changed 2023 journal title was located: *The e-positivity and Schur positivity of some spiders and broom trees*, Discrete Applied Mathematics 325, 226–240, DOI 10.1016/j.dam.2022.10.012. Its accessible preview does not expose the relevant later section. Inherited ScienceDirect denial policy was respected; no direct denied-route retry was made. The conjecture's survival in the journal is therefore a material unresolved gate. Live Omega D5 and Problems path screens are complete at the saved HEAD, but are only path screens; unrelated proof bodies are not audited.

## Exact remaining formal work

No Lean packet is delivered. It would be misleading to present the three integer coefficient computations as the requested endpoint. Required bridges: define the spider as a finite simple graph; define X_G from proper colorings (or prove a sound power-sum inclusion-exclusion construction); establish the elementary basis and uniqueness; prove the path series and the triple-deletion identity from the graph definition; prove coefficient extraction and the unique weight-25 subpartition; deduce non-e-positivity and negate the full reserved universal conjecture. The installed mathlib search did not locate a ready chromatic-symmetric-function development. This is a substantive library gap, not an arithmetic gap. The numerical scripts are diagnostics only until these semantics are certified.
