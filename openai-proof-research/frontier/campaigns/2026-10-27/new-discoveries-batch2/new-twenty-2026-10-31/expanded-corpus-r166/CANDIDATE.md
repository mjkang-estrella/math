# No qualified solution candidate

No full-scope new result or literal Lean endpoint survived this pass. Credit is zero. Two useful routes are retained below, but neither is submitted as a solution. No dummy Lean theorem, axiom, or surrogate endpoint was created, and no Lean packet is warranted at this stage.

## 327340: conditional geometric reduction, held

Source: Kiss–Vidnyánszky, arXiv:1402.5452, Definitions 2.1–2.3 and Conjecture 4.2. The scope is sufficiently small pattern-preserving shifts of the basic setup; large translations that change intersections are not counterexamples.

Take n >= 3, k >= 2 coprime, circumradius R = 1/(2 sin(pi/n)), apothem h = R cos(pi/n). Use marked vertices at angles 2 pi j/k, with translation epsilon R in each marked direction. Define

- a = 2 pi/n, phi = 2 pi/(kn), b = phi - a;
- s in {1,...,k-1} with ns congruent to 1 modulo k;
- d = 2 pi s/k and ell = (ns-1)/k.

The basic union boundary should have alternating outward normal angles theta_i-pi/n and theta_i+pi/n for theta_i=i phi. Between successive outward tips, polygon indices advance by s modulo k. Assuming that this exact sequence of boundary lines remains valid after the source shifts, the elementary support-line area identity gives

A(epsilon) = A(0) + C epsilon^2,

C = R^2 kn/2 * (cos(b-d)-cos b)/sin b,

A(0) = kn h^2 (tan(a/2)+tan(b/2)).

Under the same assumption, perimeter stays constant. Its linear perturbation sums to zero over the n sides of each polygon; all normals remain fixed. The first area variation similarly vanishes.

For completeness, for a closed line polygon with consecutive outward normals differing by Delta_i, and line support numbers h_i, the proposed identity is

A = sum_i [h_i h_(i+1) csc(Delta_i) - (h_i^2+h_(i+1)^2) cot(Delta_i)/2].

This follows by solving the two-line intersections and inserting their coordinates into the signed shoelace sum. It applies to a concave polygon only after its orientation, correct boundary intersections and absence of spurious segments are justified. Here the increments alternate between a and b, and the sums over polygon sides use sum cos^2(t a+u)=n/2 and sum cos(t a+u)cos(t a+v)=n cos(u-v)/2. Same-tip quadratic terms cancel. Cross-tip terms give C above.

The remaining scalar sign argument is short and exact. Since ns=1+ell k, b-d=-(ell+1)a. Also 1<=ell<=n-1 and -pi<b<0. If ell=n-1 then cos(b-d)=1>cos b and C<0. Otherwise cos((ell+1)a)<=cos a<cos b, so C>0. Finally ell=n-1 holds exactly when k is 1 modulo n. Thus this geometric reduction predicts exactly the source conjecture. k=1 is a single translation and has unchanged ratio.

Validation: `scripts/polygons.py` computes exposed boundary intervals by convex clipping, independently of this support formula. It tests all 277 coprime pairs 3<=n<=13, 2<=k<=41 at epsilon=0.001/(kn). `scripts/polygon_formula.py` compares the formula to clipping: maximum absolute area discrepancy about 1.02e-13 and perimeter discrepancy about 9.60e-14. Floating point cancellation makes some tiny sign differences inconclusive; this is numerical support, not proof.

**Precise gaps:** prove the stated basic-union boundary-line ordering for every coprime pair; establish an epsilon interval preserving it through the source's sequential translations; prove the nonconvex support-line identity with its orientation and union semantics; then formalize all of this literally in Lean. The small numerical epsilon is not a certified universal stability bound.

**Verdict and credit risk:** held reduction, not a proved endpoint. High Lean cost: polygon unions, boundary/perimeter/area and trig geometry. Material significance risk: this extends the source's own square perimeter/area mechanism, and could be judged an uncredited source-ingredient generalization. No novelty clearance is asserted. Do not create a surrogate theorem about C and call it the MathDB solution.

## 381182: bounded positive evidence, parked

Source Definition 17 requires edges with labels from pairwise different source components. Merely finding an ordinary label-avoiding spanning tree would miss this condition.

`scripts/snakes.py` transports cyclic necklaces along the exact source Theorem 7 hyperedge tree using Lemma 9. It constructs the chain graph and then contracts the lower-sign components. Its n=3 graph matches all 24 edges of source Example 3, not just its order or degree distribution.

At n=5 (N=11), beyond the source's verified n=3,4, the reconstruction has 20,160 chains, 20,160 labels and 120,960 edges. The quotient has 56 components of 360 chains each. After collapsing parallel edges having the same unordered endpoints and label component, there are 1,680 edge types.

A component spanning tree uses an independent set common to a graphic matroid and a partition matroid. `scripts/snakes_exact.py` implements augmenting paths for their intersection. For each of all 56 component groups, it finds a spanning tree avoiding that **entire group**. This is stronger than avoiding any one prescribed label in the group. All 56 certificates have 55 edges and distinct permitted label groups. `scripts/check.py` independently checks connectivity, acyclicity, size and label-group avoidance. Source transport/quotient semantics remain ordinary Python, not a formal certificate.

Random greedy searches first stalled at rank 54 for three forbidden groups. These are NOT counterexamples: exact augmentation reaches rank 55 for all three.

**Verdict and credit risk:** parked, no counterexample and no all-n proof. A positive n=5 instance has zero solution credit. A next substantive route needs a uniform matroid rank/cut argument for the source-defined quotient. Increasing n alone would be a parameter computation, not a full solution.
