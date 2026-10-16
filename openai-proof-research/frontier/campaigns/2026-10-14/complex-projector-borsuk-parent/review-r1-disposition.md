# Parent disposition: full B8C independent review round 1

**PASS_FULL_B8C / CONTRIBUTION_UNRESOLVED / NOT_COUNTED.** Campaign **4/10**.
The frozen two-sided proof passes the independent mathematical review without
a blocking repair. Its contribution gate remains open; this is not an
accepted substantial result or a formal verification certificate.

Review seal SHA256: `c9527d05aff931a233962ef61a0f2de62d962a5fc3375735ac5afdcacdfaaa44` (440 bytes).
Author seal SHA256: `fc997d93ac553767e1ce252e73e57ffb3c675d36b09d1949c1e8a14f6f9db9af`.
Frozen scope SHA256: `133c0d45fdd9f4a1c328dee664b142ac2cf09c6d0600fcc1ed53bdb565dea838`.
Candidate SHA256: `52256d84ffea02d6c30bccc9ff29d6cebc9f88cbb12a15f265c49b85fd8e0304`.

## Mathematical assessment

The target is unchanged: the entire complex rank-one 3-by-3 projector set
in the trace-one Hermitian hyperplane has diameter sqrt(2) and Borsuk number
nine. The lower bound allows arbitrary covering subsets; the upper bound
produces nine compact sets of strictly smaller diameter. It attains d+1 in
dimension eight and is not a dimension-eight counterexample.

Parent read the full frozen candidate and review, source-contract/reading
log, operation comparison, scope, status and verifier. Parent checked the
following deductions against the displayed formulas, adopting B1–B4 PASS:

- The open-neighborhood reduction needs no measurability. The homogeneous
  extension is continuous at zero, and the positive-integral support
  identity holds at singular PSD matrices. Orthogonal positive/negative
  spectral ranges prevent cancellation, giving the odd map from S^8 and
  the lower bound of nine labels.
- The Hesse equality locus has all twelve MUB rays. The phase convention
  and Weyl–Heisenberg translations preserve the cyclic favored-pole
  assignment. The fiducial's four favored derivative products have positive
  real parts with minimum 1/sqrt(24).
- The complex-chart score expansion retains the conjugate of
  (1+gamma*z2) in its cross term. With a=|z2| and b=|z3|, the favored
  and other trios give respectively a-b^2+epsilon/sqrt(6)-2epsilon^2
  and b-a^2-(13/4)epsilon-2epsilon^2. The cases b^2<=a,
  b^2>a with b>=4epsilon, and b^2>a with b<4epsilon exhaust the
  chart, including degenerate directions and the stated boundaries.
  The exact positive residual bounds in the review justify the decimals
  in the author proof; no sampled minimum is used.
- The compact complement is nonempty because s0 has score at most 1/2
  against each hole, whereas membership in a hole chart requires score
  greater than 1/(1+r^2). Its positive unperturbed gap and the uniform
  score-change bound 2epsilon combine with the local estimates. A second
  compactness step gives a global positive overlap margin. Closed cells
  then have attained diameters, and Bessel excludes every orthogonal pair.

These checks clarify consequences of the frozen formulas rather than
replace a failed argument. Future editorial improvements are recorded:
change “nine holes” to “twelve holes,” state the complement's nonemptiness,
print exact constant bounds, and correct the provenance sentence saying no
original repository brief exists. Neither sealed package was edited.
No Lean check or new numerical diagnostic was performed.

## Contribution assessment

Parent adopts B5 **UNRESOLVED**, without upgrading it to SUBSTANTIAL or
downgrading it to TECHNICAL/DUPLICATE on insufficient evidence. The
Hermitian lower-bound transfer and Hesse/MUB/WH geometry are antecedents.
The candidate's proposed additional operation is the cyclic assignment,
one tangent improving its four assigned poles, and the two-trio estimate
controlling entire neighborhoods, including shifted holes.

The review compares actual primary bodies on SIC classification, Hesse
incidence, Grassmann quantization and projective topology. Packing or SIC
classification does not give a worst-case covering guarantee; expected
distortion does not give a uniform guarantee for one nine-center codebook.
Parent read the comparison and its precise reading limits, but did not
independently reread those external papers in this integration. No new
literature search or worldwide priority claim is asserted here.

The unresolved comparison is exact: does an earlier complex-projective
covering construction or non-SIC WH codebook already give nine centers in
CP^2 with inf_u max_s |<s,u>|^2 > 1/2 (Fubini–Study radius <pi/4), or supply
the same hole-resolution operation? The review could not access the body
of the Mondal–Heath paper, DOI 10.1155/2008/594928. A focused contribution
follow-up should obtain that body and pursue its closest covering references,
recording theorem statements, distance normalizations, codebook sizes and
worst-case quantifiers. A missing search hit cannot close this gate.

## Integrity and next action

Parent independently authenticated the externally reported seal, manifest,
exact 30-file/5-directory membership, all payload sizes/hashes, 40 fixed
external inputs and 14 pinned Git blobs against the complete catalogue.
The inspected read-only verifier passed with the correct anchor and rejected
the wrong anchor. All 70 protected files remained unchanged. See
`review-r1-verification.json` and `verify_review_r1.py`. These results certify
identity, not mathematical truth or novelty.

Preserve the passing full proof and resolve the specific contribution
question before any acceptance, count increase, manuscript or Lean package.
No further child was launched in this integration. PCW and crossing work
remain separate. Campaign count stays 4/10.
