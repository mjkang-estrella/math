# Partial geometry component — exact interface

Namespace `Polyomino57.Diagonal`; the original `GridPoint`, `Adj`, `Step`, `EdgeConnected`, `translate`, and `witness` are the immutable source definitions. No potential implementation or finite data is imported.

## Completed kernel interfaces

* `lattice_iff`, `inverse_coordinates`, `inverse_signed`, `adjacency`, `norm`: integer signed coordinates, parity, exact integer inverse, grid adjacency, and Manhattan/max identity.
* `grown_signed_bound`, `eleven_signed_bound`: pairwise signed differences bounded by cardinality minus one, directly by frozen growth completeness. No path-size assumption.
* `signed_spans_eleven`: both actual maximum-minus-minimum signed spans lie in [1,10] for arbitrary frozen `EdgeConnected P` of cardinality 11. `lo_attained`, `hi_attained`, `lo_le`, `le_hi` expose attained extrema and bounds.
* `integral_normalizing_shift U V`: for arbitrary integers U,V, including negative values, produces e=0 or 1 and an actual integer Cartesian d with u(d)=-U, v(d)=e-V.
* `translate_to_signed_box`: produces actual translation into an exact-extrema domain with both spans in [1,10], preserved cardinality 11 and frozen connectivity. Does **not** order the spans or canonicalize parity.
* `odd_a_map`, `odd_b_map`: proved integral Cartesian D4 affine formulas for the two odd-span parity corrections. These are coordinate formulas, not a theorem assembling canonical coverage.
* `canonicalCases_card`: literal finite filtered set has cardinality 70. Its definition uses `Canonical`; enumeration is not a coverage proof.
* `mem_domain`: Cartesian domain membership iff 0≤u≤a and e≤v≤e+b, assuming a,b,e≥0. Equal signed parity is automatic for Cartesian cells; `lattice_iff` gives the reverse correspondence.
* `mem_centers`: exact literal bounds a-5≤s≤5, e+b-5≤t≤e+5 and parity. `centers_complete` needs exact extrema; `centers_sufficient` needs bounding inequalities.
* `collision_cartesian`: the four signed offsets (±4,0),(0,±4) are exactly the four Cartesian deleted offsets (±2,±2).
* `mem_witness`: proves literal diamond-minus-four membership from frozen `witness_literal` and the actual finite square.
* `placement_iff`: an actual Cartesian translation by minus the integer inverse center places P in the frozen witness iff diamond bounds hold and all collisions are absent.
* `mem_collisionGroup`, `mem_groups`, `boundary_hits_iff`, `groups_hits_iff`: exact membership and hitting semantics for literal finite Cartesian groups, including the FOUR extremal-line groups.
* `obstruction_iff`: for P in a nonnegative-parameter domain with exact extrema, hitting all original groups iff **no arbitrary integer translation** of P is contained in the actual frozen witness. Both directions are proved; it is not a test over selected centers.
* `domain_reduction`: a no-connected-card11-hitting-subset assertion for one domain yields a witness translation for each exact-extrema connected card11 subset of that domain.
* `pruning_transfer`, `pruning_iff`: generic retained-subcollection domination transfer; each original group must contain a retained group. This is the intended connection to inclusion-minimal table constraints. Groups may overlap or be empty.
* `empty_group_impossible`: an empty group makes hits impossible. `exceptional_empty_centers` and `exceptional_groups` retain the four boundary-group expressions for (10,10,1). Empty centers are never treated as an empty collision group.
* `d4_witness`, `d4inv_witness`: all eight concrete Cartesian signed permutations preserve the actual frozen witness. `d4_adj`, `d4_card`, `d4_connected` prove frozen adjacency/cardinality/connectivity preservation.
* `recover_original_translation`: if `translate t (translate d (P.image (d4 swap nx ny))) ⊆ witness`, then `∃ z, translate z P ⊆ witness`. The conclusion permits only translation of ORIGINAL P.

## Remaining mandatory gaps

1. Assemble span ordering, integer translation, and odd-span maps into a coverage theorem producing one of the 70 canonical domains, preserving all four attained extrema and a recoverable affine D4 relationship. Individual arithmetic formulas and pre-canonical normalization are closed, but this assembly is not proved.
2. Use that coverage with `domain_reduction` and recovery to prove the main `UniversalContainer 11 witness` interface from precisely the 70 finite-case assertions. No such theorem is claimed in this component. In particular, a theorem with an extra normalization premise has not been advertised as the requested endpoint.

No finite-case assertion, potential-table entry, forced-case exhaustion, animal enumeration, or SourceFormula refutation is proved here. Exact cardinality is 11 in the finite-case interface; strengthening it to ≤11 is unnecessary for integration. The frozen generated `Polyomino57.attachCheck._unsafe_rec` is partial=true but unsafe=false and axiom=false; this exact inherited declaration is inventoried, not hidden. All new origins require partial=false. Standard three axioms only. Credit 0, counts 5 additional / 35 total.
