# Independent Pinelis 373005 review: exclude from strict novelty tally

Date: 2026-10-26. **Mathematics/source PASS; novelty REJECT. No new outcome and no Lean work warranted for this lead.**

## Decisive prior full solution

The independently retrieved live MathDB API post is UUID `de01e624-feff-4146-80df-8a2b58922e0c`. Its actual complete solution body, not merely its progress summary, already gives exactly the proposed uniform counterexample and proves that both assertions fail.

- Author: **Shivam Patel** (`shivampatel`).
- Solution UUID: `52fd7f1e-d9ce-4687-bee1-a3c1accf3b94`.
- Posted: **2026-08-20T12:37:28.895537Z**.
- Exact UTF-8 body SHA256: **`76b5d25025088a827b9bd58a8b0691efa1b9e73ee5265dcbeb4f8fd5be1c832c`**.
- Public target: [MathDB 373005](https://mathdb.com/p/373005); API snapshot and full posted body are preserved under `sources/`.

The post uses X uniform on [−√3,√3], checks the exact class and moments, gives f_X(0)=1/(2√3)<1/e, and gives an explicit probability violation at δ=1/10 by exact inequalities. I checked the calculation independently: e<3 and exp(1/10)>11/10 imply the proposed exponential benchmark exceeds 1/33, whereas the uniform interval probability 1/(20√3) is less than 1/33 because 1200>1089. This proves the full claimed refutation. Its platform label “unverified” does not turn that valid, fully posted proof into an undiscovered result.

Changing the sample interval to δ=1/4 does not give a distinct mathematical outcome. Neither does writing a new Lean formalization of this old full counterexample. It earns zero strict novelty credit.

## Exact actual primary source and hypotheses

Iosif Pinelis, *One-sided concentration near the mean of log-concave distributions*, Mathematical Inequalities & Applications 29(2) (2026), 157–167, DOI [10.7153/mia-2026-29-09](https://doi.org/10.7153/mia-2026-29-09). Actual public [publisher PDF](https://files.ele-math.com/articles/mia-29-09.pdf) SHA256 `3b1f0cae5b845954abfbb7d61f833d5a4a9b797314affe2de3abf025a976f68d`; the conjecture appears on page 158 and the class is defined on page 157. I read those actual definitions, surrounding discussion and Section 2 setup, and visually inspected the first two published pages. Current arXiv history has only 2602.06804v1, dated 6 February 2026. Its same conjecture is also present in the full primary HTML.

The class includes all real random variables with a log-concave density, mean zero, and second moment one. The proposed minimization is the unconditional right-hand interval probability P(0<X<δ), for every δ>0, with the standard exponential shifted by −1 proposed as minimizer. The density-at-zero formula is also asserted. There is no hidden requirement of exponential tails, a half-line support, a mode at a prescribed point, strict log-concavity, positivity on all of R, or a conditional probability. The earlier discussion of nonnegative mean-one variables is a separate cited result and is not part of the definition of this centered class. Section 2's extra monotonicity hypotheses belong to intermediate lemmas, not the conjecture; moreover the uniform density is nonincreasing on [0,∞) anyway.

A constant nonnegative density on an interval, zero elsewhere, is log-concave: if both points lie in the support, convexity keeps the segment in it, and otherwise the right-hand product is zero. The integral is one, symmetry gives mean zero, and the second moment is (√3)^2/3=1. At zero the density is continuous in a neighborhood and equal to 1/(2√3), so the objection is not a choice of an arbitrary density representative at one point. The conjecture's own shifted exponential has a zero-density region, independently ruling out a strict positivity-on-R interpretation. The source hypotheses are all genuinely preserved.

For completeness, the candidate's δ=1/4 comparison is also correct: its uniform mass is 1/(8√3). Elementary series estimates give e<11/4 and exp(1/4)>5/4, hence e^(−1)(1−e^(−1/4))>4/55. Since 55²=3025<3072=(32√3)², 1/(8√3)<4/55. This is the same already refuted universal claim with a different witness parameter, not new scope.

## Older extremal literature

There is further explicit older evidence against any novelty claim for the density minimum. Fradelizi–Marín Sola, *Entropy, slicing problem and functional Mahler's conjecture*, [arXiv:2406.07406v1](https://arxiv.org/html/2406.07406v1), Section 3, defines the centered functional isotropic constant using density at the barycenter. In dimension one with integral one and variance one it is exactly f(0). That primary section explicitly states the sharp lower value 1/√12, attained by the uniform interval, and credits Fradelizi's 1999 result. Thus the actual sharp value of the density objective, not just the uniform comparison against 1/e, was documented before Pinelis's paper. I read this primary section and its reference list; the PDF/HTML snapshot is preserved.

The cited original is Matthieu Fradelizi, *Hyperplane sections of convex bodies in isotropic position*, Beiträge zur Algebra und Geometrie 40 (1999), 163–183. Its official [EMIS archival entry](https://ftp.gwdg.de/pub/misc/EMIS/journals/BAG/vol.40/no.1/13.html) describes the sharp section results. I have not fully retrieved/read that original 1999 proof, so the statement above is attributed to the actual 2024 primary article's explicit account rather than presented as my independent audit of the 1999 proof. This extra literature is not needed for rejection: Patel's exact earlier full posted solution alone settles the novelty gate.

## Disposition

Preserve and credit the earlier posted solution. Do not count either the uniform example, its two consequences, a different δ, or their formalization as a new discovery. No inference about the correctness of Pinelis's proved non-sharp Theorem 1.1 is made or needed here. This review concerns the false sharp conjecture and the proposed rediscovery only.
