# Candidate submission scope

Not submitted or accepted. The repaired research argument passed the
independent round-2 proof gate. This consolidated manuscript still needs
its own independent verification gate.

Proposed title: **Uniform interior gradient estimates for finite p through
a constrained affine lift**.

Exact problem: For each n>=2, do there exist alpha_n>0 and C_n<infinity
such that every bounded weak p-harmonic u on the unit ball, for every
finite p>=3, satisfies

    ||Du||_(L-infinity(B_1/2)) + [Du]_(C^(0,alpha_n)(B_1/2))
       <= C_n osc_(B_1) u,

with no restrictions on the original critical set, sign, level-set
geometry or boundary data?

Proposed answer: yes, with a nonexplicit alpha_n in (0,1/3], conditional
on the explicitly cited pinned OpenAI input theorems. The proof uses
the exact constrained affine lift, finite-effective-viscosity rigidity,
and a uniform small-solution estimate plus an unequal-parameter
quadratic norm comparison. The paper supplies the positive-viscosity
rigidity proof as an appendix. Source assumptions and standard inputs
are listed in the manuscript.

The matching MathDB record has not yet been identified. **Do not submit
this as a full solution of MathDB 405360.** That problem asks for sharp
inhomogeneous regularity for every p>2. The large-p inhomogeneous
consequence mentioned in the manuscript is only partial progress on
that broader question and is not a second finding.

Intended supporting package: manuscript PDF and LaTeX sources; precise
problem statement; pinned upstream dependency map; compact-p uniformity
audit; exact algebra checker and its scoped receipt; Lean support
sources, toolchain and mathlib pins, build command and axiom audit;
independent proof/contribution reviews with input hashes.

Formal statement to include with any deposit: **The Lean development
certifies three scalar and seven vector supporting theorems for zero-jet
ellipticity. The vector certificate works in any real inner product space;
`physical_uniform_bounds` bounds the actual form with `sqrt(e)` under
`‖a‖²+b²=1`, `0<=e<=1`, and `b0²<=b²`, without a coordinate split.
It does not formalize the local jet-neighborhood estimate, Savin's theorem,
the PDE, compactness, fitted-class rigidity or the full analytic theorem.**

Before a final Zenodo record, finalize author names, affiliations if
desired, license, and the public repository/archive reference. No author,
institution, DOI, submission identifier or priority assertion has been
invented. Final metadata and a complete artifact manifest should bind
the exact audited version; the present draft can change in response to
review.
