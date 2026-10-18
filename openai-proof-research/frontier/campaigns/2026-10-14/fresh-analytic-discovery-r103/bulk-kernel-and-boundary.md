# Geometric presence kernel: bulk transmission and a boundary counterconfiguration

Author work, not an independent gate. The original quenched D(J1) target and scope-status.json are unchanged. This note separates an interior estimate from a false unrestricted topological claim.

## 1. The unrestricted extra-arm implication is false

Take four nuclei E=(1,0), W=(-1,0), N=(0,3), S=(0,-1/2), colored respectively black, black, white, white. Insert z=(0,0). Let F be the left-right black crossing of [-2,2] x [0,2], and G that of [-2,2] x [-2,0]. The following statements hold for the cell-union crossing convention, and have strict-clearance versions.

Before insertion, the E/W Voronoi edge on x=0 is the segment 3/4 <= y <= 4/3: compare 1+y² to (y+1/2)² and (y-3)². The horizontal segment y=1 across the upper rectangle is black, so F0=1. The vertical segment x=0 in the lower rectangle is white, carried by S, and separates its left and right sides, so G0=0.

After black insertion, the horizontal line y=0 is black throughout both rectangles: its nearest site is E, W, or z. A small displacement upward or downward retains a black crossing. Thus Fb=Gb=1. After white insertion, the entire vertical line x=0 is white: z is strictly closer than E and W at every height, and any closer N or S is also white. Hence Fw=Gw=0.

Outside a disk containing all these nuclei, the diagram has exactly four unbounded color sectors, in order black(E), white(N), black(W), white(S). There are exactly four transmitted walls, not six. In particular a large surrounding annulus has four alternating arms but cannot have six alternating arms. Both tests are insertion-pivotal, and their old values differ. The obstruction is that their shared boundary passes through the changed region: the old black cap lies inside F and outside G. Full-plane connection state does not determine a crossing restricted to either half-rectangle.

All stated inequalities admit positive margins (use y=1 for F and y=-1/10 for the new G crossing). Small perturbations of the four sites preserve the example. It can therefore be implemented on an event of positive Poisson probability in any fixed bounded window by requiring one nucleus in each sufficiently small specified ball and excluding additional nuclei in a larger protective window. A remote ring of prescribed sites can protect the finite annulus from exterior cells. This is a counterexample to an unconditional deterministic arm implication, not to the proposed scaling theorem. The zero-probability issue of prescribing exact nuclei is not being used.

## 2. Interior planar transmission lemma

Assume three fillings (absent, black insertion, white insertion) agree outside an inner disk D. Assume a graph annulus A between D and an outer cycle lies strictly inside BOTH test quads; buffer the cycles so cells meeting the cycle belong to the common unchanged diagram. All geometric changes must be inside D. Consider the fixed wall diagram in A using the source embedded triangulation convention.

Cut walls at EVERY boundary contact, retaining their accesses. The diagram consists of inner-inner caps, outer-outer caps, through strands, and closed walls. Compose the inner-inner caps with the varying disk filling; discard closed loops. The only remaining freedom visible outside the outer cycle is a noncrossing pairing of the through ends. Outer-outer caps are fixed. The number k of through ends is even. For k=0 or 2 the outer connection state is fixed. For k=4 it has at most two possibilities, the two planar cap pairings. This argument does not require either original boundary cycle to have only four switches: the additional switches have already been paired off by the fixed caps. It is the planar-pairing extension of source A Lemma an:caps, not an independence statement about random annuli.

Connectivity of boundary runs is determined by the resulting pairing and their colors, as in that lemma. Since the whole annulus lies inside both quads, any portion of a test crossing inside the outer cycle can be replaced by the corresponding connection between its boundary runs without leaving either test. Thus each test is a Boolean function of this same outer connection state. If both tests distinguish the black and white insertion states, the two states exhaust all possibilities when k=4. The absent filling must give one of them. It cannot give different values to the two tests. Therefore the mixed-old event requires k>=6.

The consecutive banks of six through walls supply six alternating disjoint color arms in a slightly buffered subannulus. One obtains the banks by walking along incident triangles on the selected side of each wall, then trimming to proper crossings; intervening walls prevent different same-colored banks from meeting. This is the bank construction in source V Lemma color-arms. Boundary accesses must remain distinct even when their planar projections touch. The statement concerns alternating arms with source V's disjoint-site convention, not six arbitrary curves.

## 3. Annealed bound at microscopic inner radius

Use the conditional five-arm-plus-one-arm disjoint-witness operation explicitly used in the proof of source V Lemma color-arms. Conditional on a fixed uncolored Poisson diagram, it bounds the alternating six-arm probability by the product of the specified five-arm and one-arm conditional probabilities (finite color choices only change constants). Integrating and applying Cauchy-Schwarz and V Lemma arm-inputs, equation arm-second-moment, gives

 P(A6(r,R)) <= C (r/R)^(2+beta),  B0 epsilon <= r <= R.

Here the second-moment inputs are UNIFORM down to the mesh; no fixed-positive-radius convergence is substituted at a shrinking radius. The conditional disjoint-witness operation is inherited from the actual source proof. This is not an assertion of a product inequality for arbitrary nonmonotone Boolean events.

For a bounded spatial set K and fixed R>0 restrict insertion locations to those with a buffered B_R(z) inside both quads. An occupancy screen at rho=epsilon sqrt(H log(1/epsilon)) ensures the entire changed cell region and relevant stars lie in B_(C rho)(z), except with probability at most C epsilon^M, where H is chosen for M>5/4. This is the source V localization screen applied around the added site; occupation of a fixed finite angular cover bounds its new cell, and the common exterior remains unchanged. Enlarging constant radii supplies graph cycles.

Writing r_epsilon=1/E N_epsilon(Q*) and using source A's pivotal amplitude r_epsilon asymptotic constant times epsilon^(3/4), the integrated mixed-kernel error satisfies

 r_epsilon epsilon^(-2) integral_K P(pF pG=1,F0!=G0, z interior) dz
 <= C_(K,R) [epsilon^(3/4+beta) (log(1/epsilon))^(1+beta/2) + epsilon^(M-5/4)].

The right side tends to zero and is summable for dyadic epsilon. Multiplication by a fixed rescaled time horizon and stationary Campbell/Mecke integration gives the same vanishing expectation for the number of these bulk bad updates. Deaths have the same estimate by time reversal, with the absent configuration as base. This bound concerns an actual stationary time slice; it is not uniform over arbitrary adversarial multitime insertion histories.

## 4. Remaining full-target obligations

The counterexample prevents applying the bulk lemma in shrinking strips along test boundaries. Section6 below removes those strips for this specific nonnegative pair discrepancy using the paid single-site color-kernel bound; it does not extend the cap lemma into the strip. The Poisson space-time expansion still requires a summable forest majorant for geometric histories, control of interacting and repeated updates, and identification of all finite-dimensional laws. The quenched two-replica construction shares initial geometry. Tightness in D([0,T],H) with J1 remains separate from these finite-test generator comparisons. Earlier short-lived-particle removal was only a finite-list estimate. None of these obligations is claimed closed here.

## 5. Exact reading and attribution limits

Re-read source A build/sections/02-annuli.tex lines1-150 (connection states, full cap proof, admissible annuli definition); source V build/sections/02-inputs.tex lines1-105 and435-535 (uniform arms, planar conventions, full relevant color-arm proof). Earlier actual readings of V02 lines180-260 supply localization. These are pinned private bodies identified by source224-receipts.json. Source A has four-switch boundary hypotheses; Section2 above explicitly proves the needed cap-composition extension rather than quoting a stronger source statement. The conditional arm operation and bank construction are paid source proof operations. No additional primary body was read during this derivation. Primary reading limits in geometric-dynamics-interface.md remain in force. This is a new geometric comparison interface only, not a contribution verdict or full process proof.

## 6. Boundary removal for this pair discrepancy is paid by single-site UI

Further actual reading: V05 lines385-458, the complete statement and proof of Lemma location-ui, including removal of the occupancy cutoff. For k=1, one replica, one time, F a single increasing crossing, and weight delta_black-delta_white, the untruncated source kernel is exactly K_e(z)=E pF(z). This is a color kernel on the diagram AFTER insertion, precisely the pF in the geometric identity. Thus the source theorem applies literally here; no geometric-history extension is required.

It gives, for some p>1,

 ||r_epsilon epsilon^(-2) E pF(.)||_(L^p(B)) <= C.

The source auxiliary q_e and r_epsilon differ by a bounded factor from common calibration, as already read in V07. Let Z be the finite union of all quad boundaries and the box boundary. Holder then yields

 r_epsilon epsilon^(-2) integral_{dist(z,Z)<R} E[pF pG 1_{F0!=G0}] dz <= C R^theta,
 theta=1-1/p>0.

This includes corners and marks. Away from the strip, a location outside either quad cannot affect that crossing unless localization fails. A location inside both quads has the buffered annulus of Section2, reducing radii by a fixed factor. Consequently the WHOLE pair discrepancy in the localization box is bounded by

 C R^theta + C R^(-2-beta) epsilon^(3/4+beta) log(1/epsilon)^(1+beta/2) + C epsilon^(M-5/4).

Take R=epsilon^a with 0<a<(3/4+beta)/(2+beta). Then rho/R tends to zero, all three terms vanish, and their sum along dyadic epsilon is finite. The large-box localization failure is exponentially small. This proves a summable vanishing bound for the integrated two-crossing mixed-old defect, including boundary locations, although the deterministic extra-arm implication itself is false there.

A finite family of tests costs only finitely many pairs: outside these pair-defect events, all insertion-pivotal coordinates have the same absent bit. Coordinates which are not insertion-pivotal are unchanged by the sandwich inequality. This gives a common connection-bit description for each individual update of the fixed finite family, except for a vanishing expected number of discrepant updates in a fixed rescaled stationary time interval. It does NOT identify the rate/intensity law of those common-bit events conditional on the evolving geometry or their multitime dependence. In particular it supplies neither a color-refresh coupling of the whole process nor J1 tightness. Those are still the full-target obligations.
