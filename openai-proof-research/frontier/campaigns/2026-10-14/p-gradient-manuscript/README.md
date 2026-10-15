# Uniform finite-p gradient manuscript — candidate

The full proposed theorem is for every dimension n>=2 and every finite
p>=3, without a sign, noncriticality, level-set or boundary hypothesis.
The paper is a research draft, not an accepted or submitted result.
The independent round-2 proof gate passed the repaired four-text
research argument. Verification of this consolidated manuscript is pending.
The independent contribution review judged the bridge
SUBSTANTIAL, with bounded literature coverage and no priority certificate.

## Build and provenance

Run from this directory with Tectonic 0.17.0 available:

```sh
mkdir -p output/pdf
tectonic -X compile main.tex --outdir output/pdf --keep-logs
```

The local build used the official musl Linux release archive
`tectonic-0.17.0-x86_64-unknown-linux-musl.tar.gz`, SHA256
`8533d07f9ccbd7a65824b9e0459041bca34af1eb33daba48f59215593753a3b7`,
from [the Tectonic release](https://github.com/tectonic-typesetting/tectonic/releases/tag/tectonic%400.17.0).
Its executable was `/tmp/frontier-typeset/tectonic`. Initial compilation
retrieved the required TeX resources. An installed Tectonic plus its
resource cache is sufficient for subsequent builds. The TeX source is
also ordinary LaTeX; other engines have not been validated here.

`main.tex` contains the introduction, primary references, normalization,
lift and gradient extraction. `compact-p.tex` gives the full common-constant
argument; the other two included main sections contain the scale-selection
and effective-viscosity arguments, including quantified lemmas. The appendix
is a full publication adaptation of the internal I236 proof, not a claim
that its earlier summary independently revalidated it.

The proof reviewer received the immutable `viscous-appendix.tex`, SHA256
`1685cc94d4a0956debc413a063718b60be68074d4f2152ea167b9852f92c4e65`.
The compiled file `viscous-appendix-typeset.tex` retains that proof and
adds the round-2 presentation requirements: closure of both the PDE and
all-center/all-radius FIT under normalized limits (P4), the dimension-two
Harnack constant lift (P5), and the common semiconcavity constant on compact
positive-time cylinders (P6). Its opening states I236/I239 provenance. It
also replaces one `split` environment by `aligned` for four alignment
columns. These mathematical presentation additions require fresh manuscript
review; this is no longer a typesetting-only delta. The frozen appendix
remains byte-for-byte unchanged as review evidence. The exact diff and
input/output hashes are in `../p-gradient-manuscript-consolidation/`.

## Exact dependencies and supporting coverage

- Mathematical upstream pin:
  `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; source theorem interfaces
  are listed in `../p-gradient-proof/source-map.md` and the round-2
  map `../p-gradient-proof-r2/source-map.md`. The latter records reading
  limits and the exact four-text proof union covered by PASS.
- Full original candidate: `../../../experiments/i345_lifted_p_gradient_research/analysis.md`.
  Repairs: `../p-gradient-parent/proof-repair-addendum.md`.
- Compact-p common-constant proof and primary scan:
  `../p-gradient-uniformity/lemma.md` and its source manifest.
- Full internal positive-viscosity argument: I236 `analytic-attempt.md`,
  SHA256 `a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931`;
  its prior independent audit is I239. The appendix is a new presentation
  and is being checked against those inputs.
- `../formal/` compiles ten supporting theorems: three scalar and seven
  vector results. The vector results hold in any real inner product space;
  `physical_uniform_bounds` certifies the actual zero-jet form
  `‖h‖²+(1+e)s²-(⟪a,h⟫+b√e s)²`, including the square-root substitution,
  under `‖a‖²+b²=1`, `0<=e<=1`, `b0²<=b²`. The lower bound is
  `(b0²/3)(‖h‖²+s²)` and upper bound `2(‖h‖²+s²)`. No coordinate split
  is needed. The parent build and axiom audit are in `../formal/validation.json`;
  standard dependencies are `propext`, `Classical.choice`, `Quot.sound`.
  This does not formalize the jet neighborhood, Savin, the PDE, compactness,
  fitted-class rigidity, gradient extraction or the main analytic theorem.
- `../p-gradient-proof/checks/algebra_checks.py` verifies selected exact
  identities. Finite checks do not prove the general analytic claim.
- `../p-gradient-contribution-r1/` compares actual primary statements.
  MathDB problem 405360 asks for a broader inhomogeneous conclusion and
  is not solved by the homogeneous statement. Its large-p application
  is only a corollary, not a second acceptance.

## Remaining publication work

Independently audit the complete consolidated manuscript against the
reviewed mathematical union and new vector certificate, incorporate any findings,
finalize authorship and publication metadata, and prepare a matching
MathDB problem/submission statement. No public upload has occurred.
Build success and visual QA do not replace a mathematical proof review.
