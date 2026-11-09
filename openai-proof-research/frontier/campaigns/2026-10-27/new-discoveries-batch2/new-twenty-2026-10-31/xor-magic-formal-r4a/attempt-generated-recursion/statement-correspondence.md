# Statement correspondence

| Component | Lean declaration | Scope and limitation |
| --- | --- | --- |
| Actual outgoing slopes | XorMagic.outgoing_affine | Any scalar assignment, ordered edges and their inverse affine maps |
| Constant incidence bridge | XorMagic.incidenceB_eq_neighbor_constants | Exact Bc equals actual outgoing constants at every vertex |
| Neighbour sum | XorMagic.affine_neighbor_sum | Exact sum for the actual affine transport |
| Open/closed magic transfer | XorMagic.open_magic_of_scalar_sum; XorMagic.closed_magic_of_scalar_sum | Require scalar cancellation and lift connectivity explicitly; no chosen orientation theorem |
| Walk composite | XorMagic.EdgeTransport.along; along_append | Correct forward traversal order |
| Omega composite | XorMagic.along_omega; nontrivial_holonomy_of_omega_walk | Require OmegaWalk; length not divisible by 3 gives a nonidentity scalar |
| Connectivity | XorMagic.connected_of_affine_loop | Connected base, c outside im D, and explicit affine loop; excludes fibre sizes 0, 1, 2, 3 |
| Fixed point | XorMagic.unique_fixed_of_affine_loop | Unique fixed point of nonidentity affine composite |
| Cycle persistence | XorMagic.EdgeTransport.cycle_of_affine_holonomy | A base simple cycle and affine composite give a lifted simple cycle of exactly the same length; hence preserves length >= 3 and nondivisibility by 3 |
| Translation and connectivity assembly | XorMagic.lift_connected_cycle_of_oriented_walk | Produces c with Bc=0 outside im D, connected regular lift and same-length simple cycle, assuming an oriented OmegaWalk |
| Complement integration input | XorMagic.LiftComplementInput | A structure carrying a complement matching decomposition, not an existence theorem |
| Requested seed-lift endpoint | absent | Missing global orientation, scalar cancellation and indexed factor-cycle assembly |
| Intended universal theorem | absent | Zero qualifying credit |

## Interface for r4b

For a base `G : SimpleGraph (Fin m)`, scalar assignment `s : OrientedEdge G → Fin 3`, constants `c : OrientedEdge G → Four`, and degree d, supply `LiftComplementInput G s c d`. Its sole field is `MatchingDecomposition (affineTransport G s c).graphᶜ (4*m-1-d)`. This is the exact graph before relabelling by `EdgeTransport.label`; vertices are `Fin m × Four`. It has cardinality 4*m. No orientation or translation is chosen by the interface. r4b should construct this field for arbitrary s and c, then pass it to the future seed assembly. The graph matching decomposition already comes from `EdgeTransport.matching`. Converting to `StrongFactorCycleData` and relabelling to Bits remain explicit r4a gaps.
