# Half-order integral bridge — locally checked extension

2026-10-28. HalfIntegral.lean compiles under warningAsError with no output;
HalfChecks.lean prints all11 actual declaration types and axiom closures.
Root read all11 reports: only propext, Classical.choice and Quot.sound.
This module is NOT yet included in verify_component.py/component-hashes.json;
the latest fresh-source full replay remains12modules117declarations. Do not call
this extension a new full replay or an unconditional source theorem.

Closed results: polynomial moments integral_0^1(1-u²)^n, their proved recurrence,
exact Gamma formula, actual E_(1,1)=exp, and

 integral_0^1 exp(-x(1-u²))du = sqrt(pi)/2 * mittagReal 1 (3/2) (-x)

for every real x. The last identity uses literal exponential partial sums,
a uniform exp(|x|) bound, genuine dominated integration, and exact Gamma moments;
no special-function identity is assumed. This supplies the series-to-integral
bridge specified in ONE-DIMENSIONAL-KERNEL.md.

Remaining: obtain the complex half-order imaginary-axis formula by the proved
even/odd split, then prove the rationally weighted Laplace kernel identity
using its first-order ODE/arctangent initial value; treat zero scales. Prove
halfCross positivity, integrate with sourceClaim_of_halfCross_positive, then
fresh full strict replay and independent final gates. No acceptance/credit.
