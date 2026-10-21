# What non-Gaussianity does not establish

PREFREEZE. These checks test a proposed inference, not the truth of the stipulated source or a new theorem nomination.

## An explicit free-theory interpolating field

In the free massive1+1-dimensional real scalar triplet g=(g1,g2,g3), take real lambda and the local Hermitian O(3)-vector field

  chi_i = g_i + lambda R_i,       R_i=:g_i sum_(a=1)^3 g_a²:.

Normal ordering uses the free vacuum. Wick polynomials exist as tempered local fields in this dimension. The ambient theory is the free triplet with unique vacuum, mass gap m and S=I. The chosen interpolating field is odd under g->-g and has the same nonzero one-particle vacuum component as g.

The mixed two-point terms <g_i R_j> vanish. Cross-contractions of the two cubic vertices give

  <R_i(x)R_j(y)>=10 delta_ij C(x-y)^3,
  <chi_i(x)chi_j(y)>=delta_ij[C(x-y)+10lambda² C(x-y)^3].

The cubic vacuum vector lives in the three-particle sector, whose invariant masses are >=3m. Thus chi has a positive mass-m atom and its remaining two-point mass support starts at least at3m. The coefficient10 follows from6 contractions of :g_i³: with itself and2 for each of the two other colors; different i,j give0. The small standalone Python script enumerates these finite contractions exactly. Its success is not an independent mathematical gate.

For four distinct Euclidean points and color1, the connected four-point function has first-order coefficient

  kappa4_chi(x1,x2,x3,x4)
    =6lambda sum_(i=1)^4 product_(j!=i) C(x_i-x_j) + O(lambda²).

At one cubic vertex, only its :g1³: part pairs with the three linear color1 insertions, yielding3!=6. Two-point functions have no term linear in lambda, so subtraction of disconnected pairings does not change that coefficient. For nonnegative nonzero smooth tests with strictly separated time supports, the smeared coefficient is strictly positive because the massive Euclidean free covariance is positive off coincidence. The four-point moment and its cumulant are finite polynomials in lambda; their derivative at0 is nonzero. Hence small negative lambda gives a nonzero negative cumulant, even though scattering in the ambient theory is exactly free.

Applying the field version of Haag–Ruelle, the chi and g interpolators have the same one-particle vectors and therefore the same collision states. In particular the incoming/outgoing maps coincide. These products also show the chi-generated Hilbert subspace contains the free finite-particle scattering states and hence is all free Fock space. No new interaction is created by the nonlinear choice of interpolating observable.

At first order the connected time-ordered star graph has a free propagator on each of its three leaf legs, but no propagator on its cubic root leg. Four-leg amputation therefore kills its putative simultaneous one-particle pole. The exact scattering conclusion follows from field independence, not from trusting a truncated perturbative expansion. This provides a concrete kernel for the off-shell-to-on-shell map.

This example does NOT satisfy all the pinned nearest-neighbor construction, normalized terminal-spin identities, positive component moment measures, or source RG contracts. It only refutes the shortcut from a positive isolated two-point pole plus a nonzero (even negative) separated cumulant to S!=I. No impossibility of scattering in the specified O(3) limit is asserted. In particular it is not a substitute counterexample to the original task.

## Normalization and limits that must not be conflated

1. Field rescaling multiplies a connected fourth cumulant by the fourth power and Z² by the same power. It neither creates nor destroys a normalized on-shell transition.
2. Changing terminal H in the source construction is not an identified small-coupling expansion of a mass-normalized scattering amplitude. The source fixed-cell -2/15+o_H(1) comparison cannot be differentiated or sent to infinite scattering time without additional uniform estimates.
3. P's cutoff limits are taken first at fixed physical circumference, then circumference grows. The all-state extension retains this order. It supplies no uniform cutoff/scattering-time limit exchange.
4. A nonzero analytic off-shell function need not be nonzero on a fixed lower-dimensional variety; a distribution has still stricter restriction requirements. H pays existence of the relevant restricted object, not its nonvanishing for this model.
5. Conservation and strict convexity force the unordered pair of equal-mass elastic outgoing momenta in1+1 to equal the incoming pair. H's separately nonoverlapping iterated formula already handles the necessary cross-family overlap. There is no newly parked endpoint/overlap theorem here.

## A precise successful reduction, and the remaining task

ALL-STATE-TRANSFER pays full mass isolation from all-state counting using compact boost averaging, positive trace-class approximation by actual OS polynomial states, and positive-measure momentum sets. SCATTERING-COMPOSITION then pays the spin-triplet wave operators and the repeated LSZ relation. The scalar bound Cw is a source input; the boost/count compatibility is not offered as an independent substantial result.

What is not supplied is a particular normalized pair of incoming/outgoing triplet wavepackets, a nonzero constant c and a proved estimate |D(g1,g2;h1,h2)|>=c, or an equally complete nonvanishing argument. A source-specific projected fourth-correlation lower bound would have to control the connected subtraction, external-leg projection and scattering limits simultaneously. This round has no such estimate. That is a limit of these calculations, not a newly frozen conjecture or an exhaustion claim.
