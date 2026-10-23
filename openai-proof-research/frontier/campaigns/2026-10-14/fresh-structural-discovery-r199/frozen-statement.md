# T323C199: separable-quotient counterexamples in every uncountable Cohen extension

Frozen research statement. Source323 and all its operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. All closures and density assertions below are norm closures and norm densities unless specified otherwise. No correctness, contribution, acceptance, or campaign count is assigned here.

## Main theorem

For every ground-model cardinal lambda >= aleph_1, let Add(omega,lambda) be the forcing of finite partial functions from lambda x omega to {0,1}, ordered by reverse inclusion. ZFC, using the stipulated Source323 operations, proves that this forcing forces the following assertion:

There exist an infinite-dimensional real Banach space X_R and an infinite-dimensional complex Banach space X_C such that, for each F in {R,C},

    dens(X_F) = dens(X_F*) = aleph_1,

and for every closed linear subspace M of X_F, if X_F/M is separable, then X_F/M is finite dimensional. Equivalently, X_F admits no bounded F-linear surjection onto any infinite-dimensional separable F-Banach space.

This is a forcing theorem, with no assumption of CH, no large-cardinal assumption, and no assumption that the ground model already has a separable-quotient counterexample. The constructed Banach spaces and their completions are internal to the forcing extension. The statement does not assert preservation of a ground-model Banach space under external completion.

## Stronger construction assertion to be proved

Fix in the ground model data for the real coordinate construction in Source323, sections norming, paths, exact-pairs, and branches. Write E for its completion in the full Cohen extension and X_0 for the closed span of its coordinate functionals there. There are sets A_t of actual infinite coded paths, one for each pure or mixed operation family t, with |A_t| <= aleph_1, such that for every infinite-dimensional separable closed F subset E there are one family t, a constant delta_F>0, and aleph_1 members of A_t whose restrictions to F are pairwise at distance at least delta_F in F*.

The construction is uniform in the following precise sense: in the ground model reserve omega_1 distinct Cohen coordinates for each admissible countable-limit-ordinal/family pair (gamma,t), and choose a ground-model coding of finite paths by finite sequences of integers. The sets A_t are the resulting generic paths, constructed independently of F. For any F in the full extension, some countable set of Cohen coordinates S supports a dense sequence coding F. All distinct reserved coordinates for the corresponding (gamma,t) outside S yield pairwise separated restrictions. One valid separation constant from the source block lift U and its approximation V is

    delta_F = 3 / (8 * 500 * ||U|| * (1 + 1/8000)).

No common positive lower bound over all F is asserted. The source path-coset maps and next-color exponents then assemble these selected paths into a bounded operator B with ||B||<=1/10, B*(W*) subset J_E(E), W=E*/X_0, and closure B(X_0)=closure B(E*) equal to their closed path-coset span. The source kernel construction X_R=ker(Q-B) realizes the main theorem.

## Relative-consistency consequences in scope

If the ground model additionally satisfies lambda^(aleph_0)=lambda, the same extension has continuum lambda. In particular, Con(ZFC) implies consistency of ZFC + continuum=aleph_2 + the simultaneous real and complex counterexamples above.

Combining this negative model with the Source323 MA + continuum=aleph_2 positive model proves, relative to Con(ZFC), independence over ZFC + continuum=aleph_2 of the assertion that every Banach space of density exactly aleph_1 has an infinite-dimensional separable quotient, over either field (indeed the two signs can each hold simultaneously for both fields).

The positive conclusion here is restricted to density aleph_1. No positive model for the unrestricted quotient assertion at continuum aleph_2 is claimed. No lower consistency strength for the unrestricted positive assertion is claimed.
