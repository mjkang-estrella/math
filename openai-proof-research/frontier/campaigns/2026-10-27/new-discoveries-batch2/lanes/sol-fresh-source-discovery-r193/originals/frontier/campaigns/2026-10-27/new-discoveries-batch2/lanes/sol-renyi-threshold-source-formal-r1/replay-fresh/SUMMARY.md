# Partial formal component — NOT a source refutation

Status: INCOMPLETE. The mandatory density entropy inequality and negation of the
source threshold are not proved. No SourceClaim PASS, acceptance, paper or credit.
The campaign remains 8 additional / 38 total; this candidate has credit zero.

Work was solo, confined to this lane, without children, git operations, browser,
external messages, publication, ledger edits or package/toolchain changes.

## Source and provenance

The target is Fu–Li arXiv:2510.09206v3, printed p.2, paragraph after (1.2),
official https://arxiv.org/html/2510.09206v3, HTML paragraph S1.p6.1.
It proposes an absolute p0 in (0,1) with exponential maximization for p >= p0.
It is not numbered Shannon Conjecture 1.1. The source paragraph was read in
the actual frozen HTML. No new prior-art screening was done; the root investment
decision and independent preliminary review were read and their scope retained.

Necessary input copies only: PROOF.md, preliminary review.md, official v3 HTML.
PROOF SHA256 ca72b385e83d919fbaa97af4d55f0e7d00e949c01c8c4af07fd93ef30fef977a.
`inputs-before.json` records absolute originals, copy hashes and pinned binary /
package verification. This named snapshot was taken after proof development
began, not at the instant of initial copying. The copies made at entry still
match their originals. `inputs-after.json` repeats the comparison after replay.
No giant registry inventory was copied. No claim of worldwide novelty is made.

## Definitions and exact proved interfaces

All functions are real-valued and all integrals use real Lebesgue measure.
`convolution f g s = integral t, f t * g (s-t)` is the literal density integral.
`normalizer a = (1-exp(-a))^-1`.
`density a x = indicator [0,a] (normalizer a * exp(-x)) x`.
`exponential x = indicator [0,infinity) exp(-x) x`.
`moment p f = integral x, (f x)^p` and `entropy p f = log(moment p f)/(1-p)`.
The exponential and entropy definitions have no claimed completed comparison.

`LogConcaveDensity f` means f is nonnegative everywhere and, for all x,y and
0<t<1, f(x)^t f(y)^(1-t) <= f(tx+(1-t)y). Endpoint weights give equality.
This is the usual functional log-concavity condition, not an analytic assumption
substituted for a proof. `density_logConcave` proves it for every a>0.

`Pointwise.lean` proves, for every real 0<p<1 and a,u>=0:

    bracket p a u = (a+u)^p - max(a-u,0)^p
    0 <= bracket p a u <= (2*u)^p.

It also proves the tangent estimate `(x+y)^p-x^p <= p*y*x^(p-1)` for x>0,y>=0
and `bracket_tendsto`: for every fixed u>=0, bracket tends to zero as real a
tends to infinity. These are unconditional real-order theorems.

`Majorant.lean` proves integrability on (0,infinity) of exp(-pu)u^p and
exp(-pu)(2u)^p for every p>0, using exponential domination and continuity.

`Tail.lean` defines `tail p a = integral u>0, exp(-pu)*bracket p a u` and
proves its integrability for a>=0, 0<p<1; proves `tail_tendsto` by actual
dominated convergence over the real atTop filter; defines `J p` as the
exp(-pu)u^p integral; proves J>0 and `eventually_tail_lt_J`.
`Result.finite_tail_cutoff` gives an actual finite positive a with tail p a<J p
for EVERY real 0<p<1. This is the analytic tail core, not the source result.

`Density.lean` proves positivity of the normalizer, nonnegativity, integrability,
and normalization of the actual density. It proves the pointwise convolution
integrand is constant on `[max(0,s-a), min(a,s)]` and zero outside; proves
integrability for each s and evaluates the literal integral as interval volume
times normalizer^2 exp(-s).

`InputMoment.lean` proves power integrability, strict positivity, and the exact
formula `moment p (density a) = normalizer(a)^p * (1-exp(-pa))/p` for a,p>0.

`Profile.lean` identifies the literal convolution with

    tent a s * normalizer(a)^2 * exp(-s),
    tent a s = max(min(a,s)-max(0,s-a),0).

It proves tent=s on [0,a], tent=2a-s on [a,2a], and tent=0 off [0,2a]. It proves
nonnegativity of the convolution and integrability and strict positivity of its
p-power integral for all a,p>0. `Result.truncated_density_properties` bundles
these completed density properties with no analytic premises.

## Exact remaining obligations

1. Prove the integral identity J-Ja=exp(-pa)*tail(p,a), with Ja the actual
   integral of the tent profile to power p, including all substitutions and
   integrable subtraction. No Ja surrogate was defined to make this tautological.
2. Derive the exact convolution moment formula and strict comparison from the
   identity and tail cutoff. The pointwise profile and power integrability are
   available, but the integral algebra connecting them is not formalized.
3. Prove normalization, literal convolution formula and positive finite power
   integrals of the rate-one exponential baseline, then its entropy increment.
4. Prove the logarithmic entropy comparison and the unconditional all-real-p
   density endpoint. Define a literal density-level necessary source consequence
   and negate its existential threshold without residual premises.

No rate invariance, Shannon result, cube optimizer assertion, source claim or
probabilistic independence theorem is claimed.

## Build, audit and deviations

Read-only pins: Lean 4.34.1 SHA e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550;
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; other package pins in pins.json.
Unchanged copied guards enforce serial j1, -M2700, warningAsError, autoImplicit
false, Lean group RSS 2800 MiB / CPU210 / wall230 / nominal45ms. Helpers use
unchanged helper_guard AS/groupRSS512 MiB / CPU210 / wall230 / nominal40ms, BLAS1.
Lean is launched by guard.py with its own AS restored to infinity, not accidentally
under the helper AS limit. RSS sampling cannot exclude unsampled transients.

Failed builds and numbered preserved logs remain under logs/. Initial broad
imports and ordinary import headers hit the Lean memory cap; switching to Lean's
module/public-import headers solved this within unchanged caps. Several ordinary
type/tactic/linter failures were repaired. No cap was raised. Initial audit saw
exported theorem stubs as axioms; `import all` for every authored module loads
actual bodies for the exhaustive audit. The repaired audit cross-checks both
environment origins and module constNames, prints actual types and transitive
axioms, and rejects unsafe/partial/axiom flags. It includes generated helpers.
Native reads had two truncated displays; no exhaustive conclusion depends on
those displays. Two rejected apply_patch invocations made no changes; their
errors are retained in the session tool transcript. No forbidden proof device
is used in the compiled component.

The deterministic `component-source.zip` contains only source and verification
inputs, with no candidate olean/ilean/IR/native artifact. Fresh replay command:

    python3 replay_guard.py python3 replay.py component-source.zip replay-fresh

The destination must not exist. Replay uses only newly compiled candidate
modules and read-only pinned upstream artifacts. `replay-fresh/replay-receipt.json`
contains exhaustive declaration types/origins/axioms/flags and every build guard
receipt. A partial-component replay PASS is explicitly not a full-target PASS.
