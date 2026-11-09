# Independent review: MathDB 369172 trigonometric counterexample

Reviewer: polynomial lane, not an author of any reviewed Lean module. Date: 2026-10-26. Verdict: **PASS mathematical correctness, exact source scope and complete formal endpoint. Recommend ACCEPT as one distinct conjecture refutation under the documented-prior-art/no-known-prior-resolution standard, subject to parent acceptance and routine final packaging.** No discovery tally is changed here.

## Exact source and published-version comparison

Leonid V. Kovalev, *Sharp bounds for some segments of bounded power series*, arXiv:2507.04544v1 (6 July 2025), Conjecture 1.3; published *Arkiv för Matematik* 64(2) (2026), 273–282, DOI [10.4310/ARKIV.2026.v64.n2.a4](https://doi.org/10.4310/ARKIV.2026.v64.n2.a4). The current [arXiv metadata](https://arxiv.org/abs/2507.04544) lists only v1.

For the normalized root

    sqrt(1+z+...+z^d)=sum_{k≥0} b_k^(d) z^k,

Conjecture 1.3 requires sum_{k=0}^n b_k^(d)cos(kt)>0 for every d≥2, every n≥0, every real t. I obtained the actual published body through the public publisher PDF URL listed in OpenAlex's publishedVersion metadata:

https://intlpress.com/api/bgcloud-front/resource/pdf/volume/2110802704359354369-2110802704359354369-6ded15daeaa1ed4090d21e2f5511dfb8.pdf

A normal GET returned application/pdf; no access-control bypass was used. The published p274 was rendered and inspected. It retains exactly this Conjecture 1.3 and separately states Conjecture 1.2 about zero-free Taylor polynomials. All ten published pages were read. The inaccessible-published-body caveat from earlier screening is therefore removed. This counterexample concerns only Conjecture 1.3.

Published PDF SHA256: `67d2eae8d47c412f72aaa8314cbc6d492539dc460785f0d399efa01cace5705b`. Preprint PDF SHA256: `dd26e4e70c6d1ecc5dc9383896506ad432bcbb6285ccdb3152fc101f39dcc796`. Full third-party texts in this review folder are local audit material, not authorized release payloads.

## Mathematical audit

The exact witness is d=49, n=949, t=arccos(523/527). In the formal source modules, D denotes the number of geometric-series terms, so D=50 is the correct translation of source d=49. There are 950 summands, including k=0 and k=949.

I checked each logical bridge:

1. `sourceRoot D` substitutes geometric(D)−1 into the formal binomial series of exponent 1/2. Its square is the full geometric series, and its constant coefficient is1. `normalized_root_unique` proves uniqueness among normalized formal square roots. These equations select precisely the Taylor coefficients of the source's branch at0. No negative square-root branch is introduced. This is an algebraic coefficient identification; the formal theorem does not separately develop analytic convergence of the germ, which is unnecessary for this finite coefficient claim.
2. Differentiating B²(1−X)=1−X^D yields the displayed first-order ODE without an illicit division. The Euler coefficient extraction gives

       2k b_k=(2k−1)b_(k−1)
              +1_(D≤k)(2k−3D)b_(k−D)
              −1_(D+1≤k)(2k−3D−1)b_(k−D−1).

   The step indices and signs check directly. For D=50 the constants150 and151 are correct. Natural subtraction is guarded where needed; the k−1 term is used only for k≥1.
3. `recurrence_unique_upto` uses D>0 so every referenced coefficient index is strictly smaller. Thus the finite exact certificate identifies all source coefficients through949; the final theorem has no assumed source-coefficient or recurrence bridge.
4. The integer certificate uses B_k=4^k b_k. Multiplying the recurrence by4^k produces the factors4,4^50,4^51 exactly. The finite kernel checks cover every index0 through949, with the proper initial coefficient. Arbitrary values outside the certified range do not affect the statement.
5. The integer cosine data obey C_0=1, C_1=523, C_k=1046C_(k−1)−277729C_(k−2). Here1046=2·523 and277729=527². The real cosine recurrence and cos(arccos(523/527))=523/527 prove C_k=527^k cos(kt) through949. The arccos argument lies strictly between−1 and1.
6. The Horner fold is ascending in k. Its output is sum B_k C_k 2108^(949−k), with2108=4·527. Consequently the exact negative accumulator equals2108^949 times the source trigonometric sum. The positive scaling factor preserves the sign. No order reversal, missing constant term or normalization factor remains.
7. `explicit_source_counterexample` proves strict negativity for the actual formal source coefficients; `conjecture_369172_false` then refutes the full universal positivity statement with d=49≥2. The conclusion also refutes nonnegativity, so this is not an endpoint equality/strictness exploit.

I found no mathematical gap or source-hypothesis mismatch. Negative real part at one unit-circle argument does not prove a Taylor polynomial has a zero; no claim about Conjecture 1.2 is warranted.

## Independent exact arithmetic

The separately authored `independent_exact_check.py` does not use the four-term ODE recurrence or the three-term Chebyshev recurrence. It obtains B by directly squaring the root series:

    2B_k=4^k·1_(k<50)−sum_{i=1}^{k−1}B_iB_(k−i).

It obtains scaled cosines by repeated multiplication in Z[sqrt(−4200)] using523+sqrt(−4200). The real part divided by527^k is cos(kt), because523²+4200=527². The resulting exact accumulator is negative, has3152decimal digits in absolute value, and its decimal integer SHA256 is `39e6d391fa70984a669f8c44782ae4d24c6c4bdc290dc751173dd0066d8b8669`.

An independently checked rational bracket is

    −476/1000000 < sum < −475/1000000.

The approximate value is−0.00047532185937002401161742899345663568. The bracket and decimal approximation are supplementary review evidence; the Lean endpoint requires only the exact negative sign. Script/output hashes and the exact numerator are retained locally.

## Independent pinned replay and frozen bytes

I copied the seven final modules into `replay/formal/`, verified byte identity against the integrated candidate, and ran the unmodified root `verify_candidate.py` against these independent copies. Result: **PASS55 declarations,7modules**, Lean4.34.1, warningAsError, only `propext`, `Classical.choice`, `Quot.sound`. No admitted/custom proof assumption, unsafe code, or native_decide occurs. Main unconditional endpoints checked:

- `KovalevCounterexample.explicit_source_counterexample`.
- `KovalevCounterexample.conjecture_369172_false`.

Receipt: `replay/build/verified/audit.json`, SHA256 `01c1f72f9053dbe0501b495f19d7f7dfc5695f69b8496a040658c3a449e7e9cb`.

| Module | SHA256 |
|---|---|
| SourceCoefficients | 6e2ac35bb3707454aee671619083bdbecdfe1037933e07fe84b0a9bac98d7c20 |
| SourceRecurrence | 7860de8941bac5fa3737010e3ce619dda24ecb406b4b40e54a95972bba974cdb |
| SourceBridge | 727233ef287d55938bb96acb59eeb13d0cc906a82431b5785695a112b504b577 |
| TrigCertificate | 86cd4e317fcf9909f4fcef4a0295b396840bb7724033c69195e7bf5b6190b0a3 |
| TrigArithmetic | d1b4bba64da2f65a5a8497a9cc3090813cb7ba6ae533789042934a6bc8f7fae4 |
| TrigBridge | 81324cf9168c3a92051f67574e570a772f622d919af90f8cba5dc45d4d9bec63 |
| TrigCounterexample | e1d69c23ba47cd92091c6474344be758682263bb201208e9bdc46878baee72f0 |

## Novelty assessment and remaining limits

Fresh independent MathDB snapshot369172 records statusopen and no solutions/comments/human_solves/model_attempts. The current primary published2026paper still conjectures positivity. Targeted searches by exact title, arXivID, conjecture label, author with trigonometric positivity/counterexample, and the witness integers located no existing resolution. The source's neighboring positivity literature includes Belov1995 and Brown–Wilson1989; it discusses monotone-coefficient criteria, whereas this source family oscillates. I checked the actual primary journal metadata/abstract for Belov's1995paper (DOI10.1070/SM1995v186n04ABEH000028): its main criterion concerns monotone nonnegative coefficients, with additional sufficient positivity conditions, rather than this explicit algebraic-root counterexample. No claim is made that I exhaustively read every cited older paper.

This exact negative witness is a substantive refutation of a precisely identified, still-conjectured published statement. It is not a direct specialization of an older stronger theorem located in this audit, and it is not a formalization of an already posted solution located in the checked sources. Classical ODE/coefficient and cosine identities are proof tools, not separate new discoveries. Finite literature searches cannot certify absolute worldwide priority; that ordinary limitation does not by itself justify indefinite HOLD under the stated acceptance standard.

## Final manuscript review

I subsequently read the complete final `candidates/trig-counterexample/main.tex`, SHA256 `0fef32d1fc730f55eead14b213a3b70cd14f80499d02ce5c800283d2f388add1`. Verdict: **PASS mathematical text, formal-coverage claims, source citation and novelty scope.** The ODE extraction, corrected recurrence, D=50 translation, B and C scaling, and H950 exponent949 all agree with the formal development. The reproducibility formula for a_j, including its negative initial a1, is correct. The displayed decimal agrees with the independent exact calculation. The paper claims no n/d minimality and correctly leaves Conjecture1.2 untouched. Its attribution identifies Kovalev and both original/published references accurately. No final PDF layout bytes were reviewed here; parent handles visual QA.

One routine packaging item was sent to parent: the manuscript says the complete integer and denominator are included in the packet. At review time the integrated directory held only formal/, candidate.json, build/ and main.tex. Include the canonical integer-certificate JSON or equivalent before release. This does not affect mathematical/formal validity. An independent exact3152-digit numerator is available in this review folder if needed.

The source/math/formal/novelty and final manuscript gates reviewed here therefore PASS. Recommend accepting exactly one distinct refutation under the bounded novelty standard; parent retains count and release authority.
