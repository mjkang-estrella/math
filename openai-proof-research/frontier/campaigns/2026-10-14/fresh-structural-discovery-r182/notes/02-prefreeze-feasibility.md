# Prefreeze feasibility record

This file precedes the exact theorem freeze and the full author proof. It records the integrated construction and the interfaces that were tested, rather than replacing an old target with a weaker statement.

## 1. Select the extra operation

For a surjective map f:S_X→S_Y assume equality of the UNORDERED PAIR of sum/difference norms for every pair of unit vectors. The candidate extra operation is global sign recovery for arbitrary real Banach spheres. The paid source begins only after signs have been recovered. The whole-space phase theorem begins only after unequal-radius data and midpoint inputs have been recovered. Neither input can simply be asserted here.

Antipodality and injectivity are already paid by Tan–Gao Lemma2: a preimage of -f(x) must be -x, and equality f(x)=f(y) then forces x=y. The quotient distance

    d_P([x],[y])=min(||x-y||,||x+y||)

therefore gives a bijective isometry Fbar:P_X→P_Y. The quotient is metrizable and q_X:S_X→P_X is an honest two-sheeted covering: radius<1 antipodal neighborhoods do not intersect, and q_X is open. This is topological information actually supplied by the phase hypothesis, with no continuity assumption on f.

## 2. The topology is available at every dimension

For dimX≥3, each loop in S_X can be uniformly approximated by a normalized polygonal loop. The original and polygonal loops are homotopic by normalized linear interpolation, since they are uniformly close. The polygon is contained in finitely many two-dimensional subspaces. Choose a finite-dimensional containing space of dimension≥3 and a unit z outside those finitely many proper subspaces. Coning the polygon to z never meets zero. Thus S_X is simply connected even when X is nonseparable. Small hemispheres have charts u↦u/φ(u) into the affine hyperplane φ=1, so local path connectedness holds.

The ACTUAL covering lifting criterion now lifts Fbar q_X continuously. Its antipodal parity is constant on connected S_X. Even parity would descend to a section of the connected double cover S_Y→P_Y, impossible (a section and its negative split the total space into two disjoint open sets). Hence the lift is odd, bijective and locally a homeomorphism. If only Y has dimension≥3, use the inverse quotient map first and invert the resulting homeomorphism. This avoids assuming equal dimensions in advance.

If both dimensions are2, radial angular parametrizations identify both quotient circles with R/πZ. A circle homeomorphism has a continuous angular lift h with h(θ+π)=h(θ)±π. Local injectivity gives monotonicity; injectivity moduloπ forces degree±1. Consequently the corresponding lift on R/2πZ is an odd homeomorphism of spheres. Dimension1 is immediate from antipodal bijectivity. Thus no hidden dimension2 exception remains.

## 3. Continuous lifting is not yet metric lifting

A continuous odd lift U is still only known to preserve the unordered pair. The missing question is whether U can switch the two values at some non-isosceles pair.

For fixed x and y with ||x-y||<||x+y||, use the normalized segment z_t=((1-t)x+ty)/||(1-t)x+ty||. The planar monotonicity operation gives

    ||x-z_t||≤||x-y||<||x+y||≤||x+z_t||.

This requires neither strict convexity nor strict monotonicity: the strict gap is the one at the chosen endpoint y. The two permitted continuous target-distance branches never meet anywhere along the path. At t=0 the difference branch is forced to be zero, so it stays the difference branch through t=1. The opposite strict inequality follows by oddness and replacing y by -y. At equality the branches are identical. This closes the metric orientation step rather than assuming that a local sphere isometry is global.

The needed monotonicity has the following exact algebraic check. If b is the sphere point in the cone between unit a,c, let p=[a,c]∩R_+b. Then ||p||≤1 and p lies on[0,b]. The triangle inequalities give

    1+||a-c||=||b-p||+||p||+||a-p||+||p-c||
              ≥||b-a||+||c||.

Thus ||a-b||≤||a-c||, including flat faces. Apply the same observation from -a along the reverse semicircle for the plus norm. This is the actual classical planar proof specialized to exactly the required interface.

## 4. Source compatibility and strongest payment

Once U is an onto ordinary sphere isometry, its source defect D_q and all inverse/return maps have exactly the source's hypotheses. The common-support propagation and Darbo mechanism can be used unchanged, producing M=0 and the unique radial real-linear isometry T. No selection along a possibly enlarged ultrapower is required: the sign lift is constructed before the source's enlargement. Normalization at one chosen x_* fixes T among±T; the phase ε=f/T is even but need not be continuous.

The candidate mechanism is the combination of a global antipodal lift with orientation transport along strictly separated chord branches. The covering theorem and planar monotonicity are classical and expressly credited. The proposed contribution is their fully compatible arbitrary-space sign recovery, not either classical lemma, the source headline, or radial bookkeeping. Its substantiality and literature novelty require independent review; there is no self-grade.

Chronology: the topological route was first considered as a feasibility idea while the phase primary papers were being acquired. The actual monotonicity proof and Hatcher's operative lifting proofs were read after that tentative idea, and before this retained derivation, theorem freeze, or author-proof drafting. Those reads are disclosed rather than retroactively described as earlier inputs. Full whole-space, C(K), and2026 C0 phase proofs were read before this note. CL full-proof access remains unavailable and is not claimed.

No unresolved mathematical bridge has been identified in this feasibility construction. The next file freezes the exact all-Banach statement BEFORE the extended author proof. This is not a mathematical correctness or contribution gate.
