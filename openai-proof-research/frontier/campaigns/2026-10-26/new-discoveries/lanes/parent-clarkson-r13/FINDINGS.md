# Three-operator Clarkson target — excluded: public prior refutation

Credit0. This run found a correct independent small integer-matrix counterexample,
but the IDENTICAL source assertion was already publicly refuted in Lean on
2026-10-26. No new Lean investment, paper, acceptance or discovery count is made.

## Exact source and version status

Live MathDB372905 remains open/empty, but that is stale and is not novelty evidence.
Zhang2602.01463v2 Conjecture1.20 p5 states the proposed coefficient
(3^(p-1)+1)/2^p for arbitrary Schatten triples, upper direction for p>=2 and
reverse for0<p<=2. Actual PDF text read; the current v3 (2026-04-16) no longer
contains this conjecture. No claim about the reason for its removal is inferred.
The same assertion occurs in2410.21961v4, as the prior public repository's actual
source quotation records. Do not attribute the statement to current v3.

## Independent integer witness

At p=9/4 take
A=[[1,-3],[3,-7]], B=[[7,3],[-3,-1]], C=[[-1,-3],[3,7]].
Each of A,B,C,A+B+C has Gram characteristic polynomial t²-68t+4, so its singular
values are3sqrt2+4 and3sqrt2-4. The pairwise Grams are64I,36I,36I. Thus the exact
left side is4*((3sqrt2+4)^(9/4)+(3sqrt2-4)^(9/4)); the right side is
((3^(5/4)+1)/2^(9/4))*(2*8^(9/4)+4*6^(9/4)).
exact_check.py independently verifies all matrix identities and rational power
brackets using only integer/rational arithmetic. It certifies left>460 and
right<459, hence strict failure. A high-precision supplementary evaluation gives
a gap about2.272625; the decimal is not the certificate.

The normalized search found this family at p near2.1, then reduced the
conformal/anticonformal decomposition to integer matrices. The prior p2.5 blowup
is no evidence of a counterexample: this run's bounded normalized search at2.5
found no violation (finite evidence only). A tiny-p scalar defect is merely a
domain issue and receives no credit either.

## Decisive public prior art

The read-only trureturing registry clone at f8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada
contains Problems/zhang-2024-three-operator-clarkson-mccarthy.md and the actual
D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.lean. The earlier
witness uses two coordinate projectors and a negative rank-one projector. Parent
read the complete problem report/blueprint and copied the actual Lean source;
exact_check.py also independently verifies its Gram spectra and strict scalar
inequality. Parent does not claim to have replayed that external Lean build.

The live primary GitHub commit API identifies the original proof commit
22c3b64648689af01fa089a611812a782edcc2ee at2026-10-26T12:38:18Z, followed by
refactors; this predates the current2026-10-27 search. Immutable primary link:
https://github.com/the-omega-institute/trureturing/blob/22c3b64648689af01fa089a611812a782edcc2ee/D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.lean

A different witness at the same exponent does not restore discovery novelty.
The reverse direction, local neighbourhood argument and replacement constants
are explicitly outside our credit; the public report already discusses several.

## Evidence and limits

sources/ stores genuine v1/v2/current PDFs, latest submission history and live
MathDB record; fetches bind hashes. The external report/Lean file and public
commit API response are preserved, along with registry search outputs. Broad
web searches alone missed the existing refutation; direct registry search found
it before any local Lean work. No claim of worldwide priority or a new result.
