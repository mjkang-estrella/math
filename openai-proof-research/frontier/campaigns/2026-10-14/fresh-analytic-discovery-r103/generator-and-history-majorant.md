# Weak generators and the lifetime-history forest

Author derivation toward the unchanged full quenched J1 target. No process identification or independent verdict is asserted.

## 1. Exact stationary generator identity

Let pi_lambda be the fair marked Poisson law, L_BD the generator with death rate1 and birth intensity lambda, and L_C the generator refreshing each site's color at rate1. For bounded cylinder functions phi,psi of a fixed finite family of crossings, all the expressions below are integrable by the source one-site pivotal bound and localization. Write Delta_c phi=phi(eta+z_c)-phi(eta), and d phi=phi(eta+z_black)-phi(eta+z_white). Stationary Mecke and birth/death reversibility give exactly

 E_pi[psi (-L_BD)phi] = lambda integral E_pi E_c[Delta_c psi Delta_c phi] dz. (1)

Indeed the usual one-half in the jump Dirichlet form cancels against the equal birth and death contributions. For refresh, conditioning on the old and new fair colors gives

 E_pi[psi (-L_C)phi] = (lambda/4) integral E_pi[d psi d phi] dz. (2)

The Poisson configuration on the right of (2) is the configuration with the tested point removed; this is precisely Mecke, not a change of its conditional law.

On the common-bit event from bulk-kernel-and-boundary.md, the absent crossing vector equals either the black or white vector. Consequently

 E_c[Delta_c psi Delta_c phi] = (d psi d phi)/2,

irrespective of which bit the absent vector has. If no coordinate is pivotal both sides vanish. Outside this event the difference is bounded by a constant times ||phi||infinity ||psi||infinity times the union of pair mixed-old events. Apply the summable integrated estimate to the combined finite family of tests used by phi and psi. It follows that

 E_pi[psi (-(r_e/2)L_BD)phi] - E_pi[psi (-r_e L_C)phi] -> 0. (3)

This is weak generator agreement at stationary time zero, with the correct factor2. The pointwise conditional drift need not agree. Taking psi to be a future conditional expectation is NOT licensed: that function depends on the entire marked configuration and varies with e and time, whereas (3) was proved for fixed crossing cylinders.

## 2. An exact obstruction to inferring path law from (3)

Let a visible bit V be uniform on {-1,+1}. In model A it flips at rate cbar=(c0+c1)/2. In model B attach a hidden static bit H uniform on {0,1}, independent of V, and flip V at rate c_H, with 0<c0<c1. Both full processes are stationary and reversible. For every pair of functions phi(V),psi(V), their compressed generator bilinear forms are identical. Nevertheless

 E[V(0)V(t)] = exp(-2 cbar t) in A,
 E[V(0)V(t)] = (exp(-2c0 t)+exp(-2c1 t))/2 in B.

These differ for every t>0. Thus equality even of ALL visible cylinder Dirichlet forms cannot replace control of the hidden evolving geometry. This example is only a logical obstruction to that inference, not a counterexample to Voronoi convergence. A semigroup convergence theorem would need its actual hypotheses, such as a full form-domain approximation and a suitable lower bound, not just agreement on this fixed family.

## 3. Exact absence algebra and what it does not cancel

For an allowed presence interval h, let B_h,W_h insert at a selected location with that presence history and the indicated constant color. Let I omit the point at every time. Put R_h=(B_h+W_h)/2 and C_h=(B_h-W_h)/2. Then

 B_h-I = C_h+(R_h-I),  W_h-I = -C_h+(R_h-I). (4)

Operators at distinct selected locations commute. Therefore the product of k differences expands over subsets S of {1,...,k}, using C_hi on S and R_hi-I on its complement, with the signs of the selected colors. This is an exact inclusion-exclusion identity. Fair averaging of a single independently colored lifetime leaves R_h-I, not C_h. The geometry term cannot be thrown away as a centered color weight. Even on the common-bit event, (R_h-I)phi equals either plus or minus half the black/white jump; it is not pointwise zero. The source's color-history theorem alone therefore does not identify the geometric coefficients.

## 4. One-replica absolute majorant by the source forest proof

There is nevertheless a direct extension of its ABSOLUTE bound. Fix n observation times, finitely many polygonal tests, and |F|<=1. Let eta0 be fair critical Poisson of mesh e0. For distinct deterministic z1,...,zk and arbitrary deterministic presence/color histories hi, define

 H(eta0;z,h)=sum_{S subset [k]} (-1)^(k-|S|) F(eta0 plus particles (zi,hi), i in S).

Then |H|<=2^k. If H is nonzero, for EACH i there must be a setting of the other selected presences for which changing i changes at least one crossing at one observation time. The witnessing setting may differ with i. This implication is deterministic and uses cancellation in the difference, not a union bound over 2^k settings.

Use EXACTLY the merging forest and life probes of V05 lines190-289. The roots are polygon marks/vertices; the forest is built on selected locations. In a probe, all selected locations are outside its buffered annulus. A base-geometry occupancy screen in that buffer isolates its cells from every outside nucleus, uniformly over all selected subsets. Addition cannot remove the shielding base nuclei. Hence the diagram and colors in the probe are the same for every selected presence setting and every observation time. They are the critical base diagram with constant fair colors. This is the essential extra check compared with fixed-tessellation histories.

If changing one selected presence changes a crossing, its geometric changed region is the inserted cell (with its recolored pieces), localized inside the life probe's inner boundary. The black/white insertion sandwich implies that the corresponding inserted color is pivotal whenever presence changes that crossing. Outside the changed region, the usual four-arm necessity applies; when the probe encounters a straight side, it is four arms up to that side followed by the source three-half-plane-arm test. Roots keep corners out of the probe. The crossing and time witnessing the influence may vary, but on the probe there are only the fixed number of quad choices and one constant critical color field, so no factor exponential in the number of time-history settings is incurred.

Failed occupancy screens are handled by the SAME outermost-failed-screen decomposition V02 lines180-260 and V05 lines263-280. The screen is based solely on the base process in its buffer and is simultaneous over selected subsets; beyond the outermost failure the remaining probe is shared. Its sum costs the original arm factor up to a constant. Distinct life probes have disjoint buffers as proved in V05, so their critical probabilities multiply. Consequently

 |E H| <= E|H| <= C^k product_{lives C} A_e0(C0 max(u_C,D_C),c0 v_C). (5)

The 2^k bound and finitely many quad choices have been absorbed in C^k. No estimate is imposed on colors or geometry inside a selected cluster. Source V05 lines290-383 now apply unchanged: diameter-charge at most k, telescoping into a_e0^k product_f ell_f^(-g), and factorial forest integration yield

 ((lambda0 r_e0)^k/k!) integral_(B^k) E|H| dz <= C^k k^(-(1-g/2)k). (6)

Here lambda0=e0^-2 and r_e0 is comparable to source q_e0 by the paid calibration. Formula (6) is stronger than the required absolute bound on the averaged coefficient. Integrating arbitrary lifetime-history marks preserves it. This is a proof-level reuse of the source forest, with the simultaneous geometry-screen and presence-to-color-pivotal steps made explicit; it does not identify the limiting coefficients.

For the actual persistent base, e0=e exp(aT/2), lambda0=lambda exp(-aT), a=r_e/2, and rare spatial intensity lambda h_a with h_a<=2aT. The ratio (lambda h_a)/(lambda0 r_e0) is bounded by a constant depending on T. Thus (6) supplies a summable majorant C_T^k k^(-(1-g/2)k) for the one-replica exact lifetime expansion. The same fixed-k forest bound with gp<2 supplies location uniform integrability. It now suffices for annealed finite-dimensional identification to identify each fixed, separated geometric-history coefficient; summing before that identification is no longer the obstruction.

## 5. What is still required

The common-bit lemma fixes the effect of a SINGLE stationary update on fixed observations. It does not give the conditional law of the old cap in (4), or its joint law across a finite list of separated lifetime insertions. A local replacement theorem must retain those signed absence terms and the induced correlations with persistent geometry. The source fair-geometric-insertion cancellation may be relevant, but its actual full proof has not yet been read or imported.

For quenched laws, two replicas share initial uncolored locations. A simultaneous persistent base has intensity lambda exp(-2aT), with independent colors for the replicas. Rare initial locations can remain constant in one replica and die in the other, and they enter the pair-history expansion at order a, not automatically a². Thus source repeated-label O(q) savings must not be asserted for them. Their exact coupled replacement still needs derivation. Path tightness and J1 identification remain separate. No narrowed FDD result is nominated.

## 6. Actual reading limits

New read: source V05 lines190-383 in full (merging forest, probe localization, diameter charge, telescoping and factorial integration). Lines1-190 and385-458 were previously read. The stated extension uses precisely those operations and the previously read V02 localization section. No new primary body was read for this note. All source paths and hashes remain those in source224-receipts.json; third-party bodies stay private. Equations(1)-(4) and the hidden-rate example are direct original calculations; (5)-(6) explicitly reuse the source proof. No independent verification is claimed.
