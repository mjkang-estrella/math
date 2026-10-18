# T027O: scoped algebra support

Myeongjin Kang; no affiliation. Prose CC BY 4.0, code MIT.

This is author-side Lean support for the principal-minor rigidity step of
`fresh-arithmetic-discovery-r36/candidate027o.md`, whose SHA256 is
`e5812790dc336e2184ffbee58882fb154175554b9e23e0cacedeecac6bf48867`.
It is not an independent formal review, a full formalization of T027O, or an
acceptance decision. The frozen author packet has not been changed.

## Exact coverage

`triangle_coboundary` works over any field and any index type with a chosen
reference index. A zero-diagonal antisymmetric scalar array whose oriented
triangle sums vanish has the form x(i,j)=h(i)−h(j). Distinct-index hypotheses
are explicit; the one- and two-index cases are included.

`principal_minor_rigidity` assumes nonzero off-diagonal entries of M, zero
diagonal entries of E, the explicit stationary pair polynomials, the explicit
six-term oriented-cycle derivative polynomials, and unequal forward/reverse
triangle products. It proves E(i,j)=(h(i)−h(j))M(i,j). The proof divides by the
nonzero entries, factors the cycle identity and applies the coboundary theorem.

The names describe the intended application. Lean does **not** identify these
polynomials with Fréchet derivatives of determinant functions or prove the
reduction from stationary principal minors. Nor does it formalize generic
Cartan choices, torus density, Vandermonde arguments, surface curves, Goldman
flows, character-variety geometry, arithmetic integrality or orbit density.
Those obligations remain in the full mathematical proof and its separate
independent review. No ordered-field or characteristic-zero assumption is
hidden in the algebraic support theorem.

## Controls and trusted boundary

`Controls.lean` gives a rational 3×3 generic example to which the support theorem
applies. It also proves a counterexample to deleting genericity: the symmetric
off-diagonal-one matrix and a cyclic antisymmetric E satisfy all the displayed
stationarity identities, but E cannot be a diagonal commutator. Thus the
genericity assumption is mathematically necessary for the stated conclusion.

`rebuild.py` compiles fresh support/control objects in a new directory outside
this packet, checks declaration types and prints every declaration's axioms.
The recorded run compiled three support declarations and twelve control
declarations without warnings; dependencies are limited to standard
`propext`, `Classical.choice`, `Quot.sound`. No placeholder or extra axiom is used.
Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` are pinned.
All nine dependency Git HEADs and tracked cleanliness are checked. The shared
dependency object cache is trusted, read only, and not rebuilt from source;
only this packet's objects are freshly compiled. The lockfile, builder and
identity verifier derive from the previously recorded RCS128 support workflow.

    python3 -B rebuild.py --output /var/tmp/NEW-UNUSED-T027O-BUILD
    python3 -B verify.py --anchor EXTERNAL_MANIFEST_SHA256
    python3 -B integrity_controls.py --anchor EXTERNAL_MANIFEST_SHA256

The build output must be new and outside this packet. `--cache` and `--lean`
override machine-specific defaults, while pin/version checks remain enforced.
Identity controls create and remove copies in `/var/tmp`; they do not certify
mathematics. The external manifest anchor is recorded outside this packet in
the parent's receipt and campaign ledger.
