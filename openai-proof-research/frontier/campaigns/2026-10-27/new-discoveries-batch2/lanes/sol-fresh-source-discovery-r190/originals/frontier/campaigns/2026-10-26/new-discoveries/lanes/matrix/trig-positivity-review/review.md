# Independent review: Kovalev trigonometric-positivity counterexample

Date: 2026-10-26. Target: **MathDB369172**, UUID `7739c1b5-9697-4287-9e81-be452642b780`, corresponding to Conjecture1.3 of Kovalev, *Sharp bounds for some segments of bounded power series*, arXiv:2507.04544v1. Verdict so far: **exact mathematics and v1 source scope PASS; literature screen provisionally favorable, with an explicit unread published-version gap; complete Lean endpoint pending.**

## Source fidelity and latest record

I independently retrieved and read the actual [v1 PDF](https://arxiv.org/pdf/2507.04544v1), including the definitions and Conjectures1.2–1.3 on pp.1–2. For integer d≥2, coefficients are defined by the normalized germ B(z)=sqrt(1+z+...+z^d), with constant coefficient1. Conjecture1.3 claims Σ_(k=0..n)b_k cos(kt)>0 for all n≥0 and all realt. There are no restrictions on n relative to d or on t beyond being real. The witness below satisfies the intended hypotheses and gives strict negativity, not merely a zero or boundary ambiguity.

The **current live arXiv record** still has onlyv1 but now reports **Arkiv för Matematik64(2)(2026),273–282, DOI10.4310/ARKIV.2026.v64.n2.a4**. I verified this bibliographic record against Crossref. Its primary publisher landing is `https://link.intlpress.com/JDetail/2110802704359354369`. Both the DOI request and that public publisher landing returnedHTTP403. I have **not read the2026 published body** and therefore do not assert that its conjecture is unchanged or unresolved there. Public author-repository inventory did not expose a newer copy. This is a real latest-source limitation to retain in any novelty statement.

The live MathDB snapshot is open with no posted solutions/comments at review time. Its extra references to arXiv:2110.11549 and0806.3046 are mismatched metadata: the actual primary records concern Schubert-matroid Ehrhart polynomials and a(q,t)-Catalan filtration, respectively. They do not substantiate the claimed2008 first-statement date for this trigonometric conjecture. No claim about an earlier origin should be copied from this field without separate evidence.

MathDB369171 / source Conjecture1.2 is a **distinct zero-freeness question**. A negative real part of one Taylor polynomial at a unit-circle point does not establish that the polynomial vanishes in the disk. This review makes no zero-freeness refutation claim.

## Independent exact certificate

The originating worker found d=49,n=949 and cos(t)=523/527. I independently verified the sign by a different coefficient algorithm, starting from the defining square identity rather than the worker's binomial-product convolution.

Let B_k=4^k b_k. Comparing coefficients of B(z)^2=1+...+z^49 gives

    B_0=1,
    2B_k=4^k·1[k≤49]−Σ_(i=1..k−1) B_i B_(k−i)  (k≥1).

This recurrence uniquely determines all the source coefficients because its constant term is1. The independent script computes these integers through949, checking divisibility by2 at every step. Set p=523,q=527 and compute

    C_0=1, C_1=p, C_k=2p C_(k−1)−q² C_(k−2).

Then C_k=q^k ChebyshevT_k(p/q). Since−1<p/q<1, the real angle t=arccos(p/q) exists and ChebyshevT_k(p/q)=cos(kt). With R=4q=2108, compute H_0=B_0C_0 and H_k=R H_(k−1)+B_kC_k. Exact integer arithmetic gives

    H_949/R^949 = Σ_(k=0..949)b_k cos(k arccos(523/527)) < −1/2500 < 0.

The decimal value≈−0.000475321859370024 is informational; sign and the displayed rational upper bound were checked by integer inequalities. Reproduction: `check_integer.py`; full exact numerator/denominator and integer-coefficient digest: `integer-certificate.json`. The coefficient-integer SHA256 is `ed57ee4d0209cb93f5b2a1ae21d40ab684e2b8c672010233284f81d2ed1f2940`.

An earlier rough angle cos(t)=131/132 gave a positive value and was correctly discarded before any proof claim. It is not part of the valid certificate. The final523/527 sign agrees with the originating worker's independent Fraction/binomial-product calculation.

## Four-term recurrence correction

The source-root identity B²(1−X)=1−X^D, D=d+1, yields

    2(1−X)(1−X^D)B'=[1+(D−1)X^D−D X^(D−1)]B.

I independently extracted coefficient X^(k−1). The correct recurrence is

    2k b_k=(2k−1)b_(k−1)
      +1[k≥D](2k−3D)b_(k−D)
      −1[k≥D+1](2k−3D−1)b_(k−D−1).

The originating worker caught and corrected an earlier mistaken last coefficient2k−D−3 before certificate generation. The corrected value2k−3D−1 follows because the right-hand coefficientD−1 is combined with the left-hand derivative contribution2(k−D−1). The defining root, ODE, direct coefficients and negative witness are unaffected. Final formal modules must use the corrected recurrence.

## Literature screen and remaining gates

Live searches included the exact title, identifier, author plus Conjecture1.3/positivity/counterexample, the published DOI, and square-root/trigonometric coefficient phrases. I found the original source and mirrors and related classical trigonometric-positivity literature; no primary earlier full resolution or matching counterexample was located. Search absence does not establish exhaustive priority. The inaccessible published body is a separate unresolved check, not evidence that a resolution exists or does not exist there.

The negative value rigorously refutes the complete universal statement in the actual v1 source. It is substantive and does not depend on changing the branch, coefficients, truncation convention, angular domain or parameter interpretation. Acceptance as a strict new discovery remains conditional on the documented literature gate and full source-to-certificate Lean bridge. Formal work is proceeding in a separate owned lane, `matrix/trig-positivity-formal/`; this report does not yet certify that evolving code.

Source snapshots, live corpus body and provenance hashes are preserved in `sources/` and `provenance.json`.

## Supporting formal source bridge completed

The separately owned `matrix/trig-positivity-formal/` lane now provides20 fully replayed supporting declarations. It constructs the normalized root unconditionally with Mathlib binomialSeries composition, proves its square and constant coefficient, identifies every other normalized root with it, derives the corrected four-term recurrence directly, and proves exact coefficient agreement against a finite recurrence certificate. Fresh isolated Lean4.34.1 replay passed with warnings-as-errors and only propext/Classical.choice/Quot.sound. Receipt: `../trig-positivity-formal/build/fresh-audit-9upmcg0c/receipt.json`; hashes and APIs are in that lane's `manifest.json` and `PROOF.md`. The parent owns final assembly with the originating worker's numerical certificate and the cosine/arccos bridge. This supporting-module PASS does not assert that the final combined endpoint or manuscript has yet been independently replayed/reviewed.
