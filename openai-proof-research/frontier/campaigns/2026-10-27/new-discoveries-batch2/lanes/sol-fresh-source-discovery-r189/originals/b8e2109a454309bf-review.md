# Independent B8C formal support review

**Verdict: PASS_SCOPED_SUPPORT. Full B8C formalized: false. Count change: zero.**

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Third-party compiler, libraries and mathematical sources retain their rights.

This verdict binds the author output manifest
`28429901ed26db71aaa1bc3b4b7c62c1f2c38f945510e04ba4e4f48eb5893700`,
Lean source `8c6863344596404bf7f8e13e341972510f3ad7d4fa63308a9d31872a9d947cab`,
and coverage `705df89da3ec6ef20eb0013d3c24a2839b6f340357d52bb23bc30a79470871d9`.
The original author package has exactly 57 sealed payloads. Its explicitly
unsealed `.replays` are not author inputs. This review copies only its sealed
files, then retains its own fresh replay logs under the copy. The review's
outer manifest seals those new logs too, without a replay exclusion.

The full mathematical target is unchanged: the entire complex rank-one
projector plane in trace-one Hermitian R8 has diameter sqrt(2) and Borsuk
number nine. The upper statement requires nine actual sets of strictly
smaller diameter; the lower statement concerns every cover by at most
eight arbitrary subsets, without measurability or other regularity.
This review does not replace its human proof or independent contribution
gate. Candidate, scope, prior proof-review and contribution-seal identities
are recorded in input-manifest.json.

## What was actually compiled and inspected

I read every line of BorsukLocal.lean, Controls.lean, Checks.lean and
ControlChecks.lean, all executable Python in the support package, its
coverage/configuration/provenance, the entire frozen candidate and scope,
and the entire independent proof review. I then read the fresh compiler's
complete type and axiom output for all 19 support declarations (three
definitions and 16 theorems) and all 13 control theorems. No extra local
axiom, sorry, admit, unsafe declaration or native_decide is present.
Every printed dependency list consists of propext, Classical.choice and
Quot.sound. There is no upstream theorem inserted as a Lean axiom.

The independent rebuild ran the inspected rebuild.py from the copied
package, with an explicit absolute dependency-cache path. It copied only
the four Lean sources into a new temporary directory and compiled
BorsukLocal.olean and Controls.olean there. That temporary directory was
first in LEAN_PATH; the remaining entries were the pinned dependency
libraries. I checked those libraries contain no BorsukLocal.olean or
Controls.olean. No author support object was copied or used. The temporary
objects were deleted by the runner after the check. The source hashes in
the new receipt equal the independently anchored files.

The fresh compilation, positive controls, full type/axiom printing, and
exact rational semantic controls all exited zero without warnings. The
finite grid exercises 60 first-branch, 36 large-branch and 20 small-branch
instances, including 80 actual-chart instances. These numbers are bounded
diagnostics; the universal statements are supported by the Lean proofs.

## Mathematical scope and interfaces

The definitions are exactly
`favored = a-b²+(2/5)eps-2eps²` and
`other = b-a²-(13/4)eps-2eps²`.
The branch theorem assumes a,b nonnegative, b<=1/10 and
0<eps<=1/50. It splits b²<=a versus a<b², then b>=4eps versus b<4eps.
These splits cover all parameter scales, including equality on b²=a,
b=4eps and eps=1/50. At a=b=0 or b=0 the first branch applies; at a=0,
b>0 the two second-region branches cover every relative scale. No complex
direction or phase has been restricted in the scalar theorem: phase
selection is an external input needed to turn arbitrary complex chart
coordinates into its two actual score estimates.

The first branch obtains 9eps/25. In the second region, squaring
0<=a<b² gives a²<b⁴, while b<=1/10 gives b⁴<=b/1000. The large branch
therefore gives a strict 353eps/500 margin. The small branch uses
b²<16eps² and obtains the strict eps/25 margin. At b=0 the second-region
hypotheses are impossible, which does not make the exhaustive theorem
vacuous. The positive controls include origin, first-boundary, large-boundary
and small-scale instances inside the actual chart.

The radical bounds are exact: 2/5<1/sqrt(6) and
2sqrt(2)+1/sqrt(6)<13/4. The radius is exactly 1/(12sqrt(3)); its squared
value is 1/432. The chart condition a²+b²<radius² implies a,b<1/20 and
1+a²+b²<2. Rational replacements weaken the estimates in the correct
directions. Positivity of the normalization follows from squares and does
not require division by a possibly zero chart coordinate.

`two_trio_scaled_positive` assumes F and O: strict lower control of E1
by the favored radical expression and weak lower control of E2 by the
other expression. `local_score_improves` specializes E1 and E2 to
2(1+a²+b²)(1+eps²)(x-1/2) and the corresponding expression for y.
It does not construct x or y, select a trio member, prove a tangent
estimate, or establish those hypotheses for geometric scores. These are
genuine conditional statements; consistent scalar choices exist (for
example a=b=0, eps=1/50, x=y=1). Their application to particular scores
comes from the external candidate's Lemma 11, not that arbitrary example.

The two complex identities quantify over arbitrary q,D in C and real
eps,b. Expansion has the cross term
`2 sqrt(2) eps Re(conj(1+q) D)`, with the conjugate on precisely 1+q.
Division uses the positive denominator
2(1+normSq(q)+b²)(1+eps²). The candidate identifies q=gamma*z2 with
|gamma|=1, b=|z3| and D with the bra coefficients of its attached tangent.
That identification and the required norm equality are not in this Lean
file. The identities are nevertheless exactly the scalar complex
expressions of Lemma 11 and prior proof-review B3; there is no conjugation
swap or omitted epsilon normalization.

`complementary_margin` is the scalar consequence of eta>0,
eps<=eta/3, M0>=1/2+eta and Meps>=M0-2eps. It legitimately does not
need eps positive for that arithmetic implication; geometric application
selects a positive eps externally. `bessel_cap_incompatible` is only
the contradiction between two scores at least 1/2+delta, delta>0, and
their sum at most one. It does not prove Bessel's inequality.

The package does not define CP2, projectors, the Hermitian ambient space,
its dimension or the projector distance formula. It does not formalize
the arbitrary-cover reduction, PSD integral, odd sphere map or
Borsuk–Ulam; Hesse/MUB incidence and equality classification; covariance,
favored derivatives, trio selection or Cauchy–Schwarz; compactness and
existence of eta/global delta; nine-cell construction, Bessel itself or
attainment of strictly smaller diameters. In particular, neither half
of the full B8C conclusion is a Lean theorem here. coverage.json correctly
states all these limitations. No blocking discrepancy was found between
its claimed scope and the compiled statements.

## Rejection controls

I independently reran all five source mutations and read all their logs.
They reach genuine proof failures, not import, parser or name failures:

* 19eps/50 in place of 9eps/25 fails the arithmetic proof; the existing
  origin control attains exactly 9eps/25 at eps=1/50.
* eps<=1/4 in the favored branch fails; at a=b=0, eps=1/4 the favored
  expression is negative while the asserted margin is positive.
* 4eps/5 in place of 353eps/500 fails; a=0, b=1/25, eps=1/100 satisfies
  all hypotheses and the stored control disproves the stronger bound.
* Allowing delta=0 in cap exclusion fails at x=y=1/2.
* Removing the conjugate produces an unsolved polynomial identity with
  opposite signs on the imaginary cross term. At q=D=i and eps=1 the
  cross-term discrepancy is nonzero. The two unused-simp warnings in
  that mutant are incidental; the decisive failure is the displayed
  unsolved algebraic goal.

The semantic script tests the failure-marker predicate. In addition I
ran the actual checked_run.py wrapper on a child that prints SOME FAIL
and exits zero. The wrapper exited one and reported child exit=0; raw
logs are in runner-control. Thus an exit-zero printed failure cannot be
accepted by this exercised runner. No numerical experiment supplies a
missing geometric proof.

## Trust boundaries, rights and conclusion

The toolchain reports Lean 4.34.1, commit
5045d0056413266e57c625dcd7c365b10e377c52; its executable SHA256 is in
the fresh receipt. All nine dependency HEADs match lake-manifest.json,
including mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Their tracked
working trees were clean. This checks source revision and tracked state,
not a source-to-object reproducible build. Precompiled dependency objects,
Lean's standard library/compiler/kernel and runtime remain trusted. I did
not rebuild or fully byte-authenticate those caches or independently
verify a compiler distribution signature. They were only read. There was
no network retrieval or upstream-truth audit in this formal review.

Original helper provenance and MIT/CC BY rights are preserved in the
copied package. The input manifest binds the historical author files;
the output manifest binds every review payload, including fresh logs and
the verifier. verify.py requires an externally supplied manifest hash
before parsing, checks exact file/directory membership, rejects symlinks,
rechecks the original package and input anchors and the fresh source/log
links. It is an integrity verifier, not a replacement for this semantic
audit or a way to derive mathematics from hashes.

PASS_SCOPED_SUPPORT applies to these exact 16 scalar/algebraic support
theorems and their disclosed interfaces. It is not a full B8C formal PASS,
publication approval, renewed contribution verdict or campaign count.
