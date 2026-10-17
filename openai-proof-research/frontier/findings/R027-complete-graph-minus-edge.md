# R027 — The ordinary crossing number of the complete graph minus an edge

**Accepted as the fifth substantial result of the 2026-10-14 ten-additional
campaign.** This is internal acceptance under the stipulated pinned upstream
theorems, after independent proof, contribution, manuscript and scoped formal
reviews. It is not external peer review or a worldwide priority certificate.
The path-product application is part of this one result.

For every integer n >= 2 and every edge e of K_n, put

    Z(n) = floor(n/2) floor((n-1)/2) floor((n-2)/2) floor((n-3)/2) / 4.

Then the ordinary crossing number is

    cr(K_n - e) = Z(n) - binom(floor((n-1)/2), 2)
                = floor((n+2)/2) floor((n-1)/2) floor((n-3)/2) floor((n-4)/2) / 4.

There is no restriction to straight, convex, rectilinear or two-page drawings
in the lower bound. For every m >= 4 and n >= 1, with P_n the path of n edges,

    cr(K_m box P_n) = (n-1) cr(K_(m+2) - e) + 2 Z(m+1)
      = floor((m+1)/2) floor((m-1)/2) floor((m-2)/2)
        [n floor((m+4)/2) + floor((m-4)/2)] / 4.

The full [15-page paper](../campaigns/2026-10-14/kn-minus-edge-manuscript-r2/main.pdf)
has SHA256 `7108d83f47b34fe7668d096bfcc90cbacd538e2f34984a742e824f139bc45b33`.
Its full statements and proof Sections 2–6 are byte-identical to the original
independently audited manuscript. Revision r2 corrects attribution, formal
coverage and standalone verification, without narrowing the theorem.

The new lower-bound range is odd n >= 15. Even orders and odd orders <= 13
are credited antecedents, as are the classical upper bound, Harary–Hill and
the Ouyang–Wang–Huang product identity. The new product lower-bound input is
odd m >= 13 **and n >= 2**; at n=1 its coefficient vanishes. The contribution
review compares missing-pair cycle tests, mixed orthogonality, the twisted
rectangular detector, and localization/descent avoiding both deficient stars
against the primary literature. Its comparison is bounded; inaccessible
sources and indirect attributions remain disclosed in the paper/source map.

The paper exposes six upstream premises from OpenAI/math at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`: drawing normalization, cycle
pairing, interpolation weights, rectangular detector nonsingularity,
Harary–Hill, and the explicit upper drawing. Their truth is stipulated by
the campaign. The changed missing-edge argument is proved separately.
OWH Corollary 5.1 is cited from the published body; its antecedent proof
chain is not claimed as independently re-audited. The sufficient cycle-test
condition is not misrepresented as necessary.

The independent gates are:

- [Full proof](../campaigns/2026-10-14/kn-minus-edge-proof-r1/review.md):
  PASS_FULL_CLAIM_UNDER_STIPULATED_UPSTREAM; SHA256
  `1d18d360eb4a50ae801c00b56ffe377b599c9c28c9ecd4cb3753e559f45aa111`.
- [Contribution](../campaigns/2026-10-14/kn-minus-edge-contribution-r1/review.md):
  SUBSTANTIAL_ONE_PACKAGE; SHA256
  `a481ddd9c10bb938f587cd1e2ad9baa756d8ae7ae4c37c2bae3a48023395f557`.
- [Formal support](../campaigns/2026-10-14/kn-minus-edge-formal-review-r1/review.md):
  PASS_SCOPED_SUPPORT; SHA256
  `bbb0344dda8194ef776a8c4bc68a8d44894e6cee178fe019a78cfd962f4d3773`.
- [Manuscript revision](../campaigns/2026-10-14/kn-minus-edge-manuscript-review-r2/review.md):
  PASS_REVISION, no required fixes; SHA256
  `ede4c4a0e5c029d1db52d717584e13eb70fe3e5036eba173573cdb52664e04ad`.

**The full crossing theorem is not formalized.** The compiled 47 supporting
theorems and 17 definitions cover finite tensor kernels, dimension bounds,
weighted diagonal nondegeneracy, mixed-test identities, twisted detection,
localization budgets, isolation/root counting and conditional descent.
Drawing topology, concrete global/local substitutions, four-prime divisibility,
instantiated kernel descent and both evaluation injections, orientation/count
comparison, the even/upper assembly and product theorem remain prose. U4 is
an explicit theorem argument, not a new axiom or a proved upstream theorem.
The [coverage supplement](../campaigns/2026-10-14/kn-minus-edge-release/FORMAL-COVERAGE.md)
preserves these limits.

Fresh Lean 4.34.1 compilation from copied sources passed the core, 9 author
controls, 16 independent controls and four type/axiom queries; outputs match
the frozen audit. Pinned dependency objects are trusted setup. The independent
revision audit ran 43 verifier scenarios and inspected all 15 PDF pages.
The parent authenticated 40 review payloads and 383 fixed inputs, reproduced
the independent arithmetic receipt exactly, and retained all observed bytes.
These finite checks and hashes support reproducibility, not the all-order proof.

The [local release](../campaigns/2026-10-14/kn-minus-edge-release/README.md)
contains 261 files, including its bundle manifest. Archive
`output/release/r027-complete-graph-minus-edge-v1.zip` is 1,750,817 bytes,
SHA256 `a98ee88f40ab1f935a285fad0a179487d5fe36a54cd0e73bc15b5d833b3aa481`.
Clean extraction, public manuscript verification, formal payload verification,
pinned compiler/dependency setup and byte-identical deterministic reassembly
pass. Wrong anchors, tampering, missing/extra files, symlinks, duplicate ZIP
members and traversal entries are rejected. See the
[final receipt](../campaigns/2026-10-14/kn-minus-edge-parent/final-package-verification.json).
The optional stale scratch-location wording is clarified in the outer release
without altering frozen manuscript bytes. Historical pending/count records
retain their original meaning; this record supplies the later acceptance.

Author: Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original
code MIT. Local Zenodo/MathDB metadata are prepared. No public upload,
submission, DOI or external endorsement is claimed. Campaign continues at 5/10.

## Public publication

Published 2026-10-17 UTC: [Zenodo manuscript and supporting package](https://zenodo.org/records/23430013), DOI `10.5281/zenodo.23430013`; [MathDB paper](https://mathdb.com/abs/2610.00027). Files and metadata were verified; see the [submission receipt](../campaigns/2026-10-14/submissions/README.md). Earlier pending-submission statements above record the acceptance-time state. Publication does not imply external peer review.
