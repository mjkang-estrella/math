# Parent reconciliation and scope correction

26 October2026. Parent authored the candidate; this addendum is not independent review. Keep the original preliminary report unchanged. Candidate credit0, campaign12/30.

## Material prior-art correction

The reviewer located MathOverflow248816 (2016), with Gjergji Zaimi answer248836 giving Q(x)=x⁴−1, and Fedor Petrov answer248822 giving another family. Parent independently retrieved the complete question and both answers through the official StackExchange API; JSON snapshots retained. The asker's later nonnegative-coefficient addendum has no separate answer in these snapshots.

The review's assertion that the differential inequality is NOT translation invariant is **false**. For R(x)=Q(x+c), R′(x)=Q′(x+c) and R″(x)=Q″(x+c), so its normalized expression is exactly Q's expression at x+c. Specifically,

    R(x)=(x+2)⁴−1=x⁴+8x³+24x²+32x+15,
    4RR″−3(R′)²=−48(x+2)² ≤0.

All five coefficients are strictly positive, and R has nonreal roots −2±i. Thus even the nonnegative-coefficient converse (source Conjecture3) already fails by an immediate translation of the 2016 public example. Under this campaign's substantive-new-result standard it receives **NO novelty credit**. The bare converse, its positive-coefficient variant, and our alternative quartic counterexample must not be counted as new discoveries.

The **only candidate discovery basis** is source Conjecture1 / MathDB338076: a literal positive-coefficient elementary-symmetric sum with universally concave positive diagonal fourth root but strict midpoint failure inside the positive orthant. All61formal declarations remain true and unchanged; the companion nonreal-root endpoint is explicitly uncredited. This is one prospective source-question outcome, not two. The manuscript, candidate metadata, ledger and proof notes have been rescoped accordingly. Whether Conjecture1 was previously refuted remains subject to the final independent bounded-prior-art check.

For context, the polarization of R is product_i(x_i+2)−1, not our f. Its fourth root is in fact covered by the concavity construction in Andrica–Rădulescu–Rădulescu2019Theorem4.17 on the relevant positive domain. The translated old example does not give our midpoint failure.

## Other review qualifications

The review correctly states that our P is positive for all x>0. Its stronger ancillary statement that P>0 *exactly* above the largest real root is false: a positive-leading quartic with its two real simple roots negative is also positive to the left of the smaller real root. The exact positivity set is the union of the two exterior intervals. No global-positivity assertion is used in the Lean proof or manuscript.

The review's source/refinement/novelty prose is preliminary; its claims that no formal/paper exists refer to the original assigned freeze fea5692b66. Parent completed61declarations and a paper while that review ran. The final independent replay/manuscript review is separate.

## Previously unread citing chapter now obtained and inspected

Parent directly fetched publisher DOI10.1007/978-3-030-27407-8_4 as a full95-page PDF (HTTP200), saved sources/andrica-radulescu-2019.pdf and its complete text in the parent lane. Thus the preliminary report's paywall limitation is superseded for this source. Parent read **all of Section5**, pp166–183 (Convexity of Symmetric Functions), plus the relevant Theorem4.17, introduction/scope and references. Do not call this a full-body reading of all95pages.

Section5Theorems5.3/5.4 reproduce Lachaume's quadratic sufficient criterion and adjacent-degree two-term concavity;5.10extends the latter with powers. Remaining5.5–5.27 treat products/powers/ratios of individual elementary symmetric functions and homogeneous/quasiconcave constructions. None states diagonal-concavity sufficiency for general inhomogeneous sums or refutes it, and no five-term quartic/midpoint construction was found. Section5's only direct Lachaume attributions are these known positive results. Theorem4.17 proves concavity for products of nonnegative concave functions minus a convex n-th power, explaining the translated Zaimi polarization. It does not apply to the candidate's five-term sum. This is an actual nearest-citing-body comparison, not an inference from title/abstract or citation counts.

Parent also inspected the2017thesis conclusion pp180–181 and literal Conjectures1/3; these retain the source questions. The printed implication chain in that conclusion is not used as a mathematical premise. Parent read the latest2018arXivTheorem2.7(d), Remark8/conjecture and conclusion; this remains the known real-rooted-diagonal sufficient criterion. Reviewer calling an arXiv copy the actual typeset JMP source is not evidence that the typeset body was separately inspected. No absolute priority/complete citation census/subscription-index coverage claim is made.
