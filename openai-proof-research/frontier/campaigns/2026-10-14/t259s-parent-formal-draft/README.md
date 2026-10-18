# Provisional relational support retained for technical T259S

Original code MIT; prose CC BY4.0; Myeongjin Kang, no affiliation.

T259S passed independent full-scope proof review but received a TECHNICAL contribution verdict. This packet is retained support, earns no result credit, and has no independent formal review. It was started while contribution review was pending; no manuscript or formal-review escalation follows.

`Propagation.lean` proves four general theorems: consecutive related vertices have related endpoints; a row with known bridges, whole endpoints and all but one distinguished edge determines the missing edge; availability on **every point** in each base fiber propagates through the one-exceptional-position interface; one-sided layer coverage supplies every edge. Surjectivity of the exceptional row map, injectivity of the base shift, the supplied bridges, quotient-coordinate identities and coverage are explicit hypotheses. None is presented as automatically established for a measurable group action.

`Controls.lean` proves finite equality-relation examples showing why a second missing edge, an absent bridge or missing endpoint agreement break the elementary inference. A two-point-per-fiber example proves that fixed representatives in all fibers do not imply all-fiber availability. These are semantic examples, not compiler-mutation tests or complete model-level counterexamples.

Not formalized: free-group quotient substitutions, the amalgam, actual right-action instantiation, Borel graphings, marker measures, cost, Bernoulli tensor decomposition, spectral gap, weak mixing, source lower bound, full T259S or contribution. No theorem is replaced by an axiom. No `sorry` is used. The final compilation receipt lists the kernel dependencies explicitly.

Run `python3 -B check.py --output NEW_EXTERNAL_DIRECTORY`. It uses the pinned local Lean4.34.1 binary and existing read-only dependency cache, checks package revisions and tracked cleanliness, compiles fresh copies in `/var/tmp`, prints exact types and axiom dependencies, and removes build scratch. Paths are defaults for this workspace, not a portable dependency installer. The lockfile records the dependency revisions. Output must be a new directory. Parent run: `../t259s-parent/formal-draft-validation/`.
