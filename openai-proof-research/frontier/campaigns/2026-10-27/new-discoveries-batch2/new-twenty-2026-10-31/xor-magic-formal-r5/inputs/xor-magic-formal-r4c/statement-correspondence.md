# Statement correspondence

| Component | Declaration | Exact scope |
| --- | --- | --- |
| Proper colouring | FactorColouring | Proper on both first factors everywhere |
| Seed interface | ColouredSeed | LiftSeed plus true start, genuine simple walk, exact indexed binding and OmegaWalk |
| Four seeds | Seed16Closed4.coloured; Seed16Open5.coloured; Seed32Closed4.coloured; Seed32Open5.coloured | Finite kernel-decide certificates |
| Chosen slopes | chosenSlopes; chosen_outgoing; FactorColouring.reverse | Actual inherited ordered-edge convention; inverse on reversal |
| Scalar sum | scalar_colour_sum | Actual neighbours sum to d • x + x |
| Parity cancellation | chosen_open_scalar; chosen_closed_scalar | Odd open / even closed, no scalar-sum hypothesis |
| Plain lift | chosen_lift_open; chosen_lift_closed | Translation in ker B outside im D, regularity and literal connected magic at n+2 |
| Literal existence | chosen_open_exists; chosen_closed_exists | OpenExists / ClosedExists at n+2 from a coloured seed, d≥4 and parity |
| Colour persistence | FactorColouring.lift; directed_lift | Projection, every actual lifted edge |
| Cycle persistence | persistedCycle | Indexed ColouredCycleData in first two lifted factors, same length, at holonomy fixed point; complement input explicit |
| Product assembly | chosen_seed_lift_data | ColouredLiftSeed on Fin m × Four, with complement input for all translations |
| Requested iteratable seed lift on Bits | absent | Relabelling and indexed-cycle-to-walk reassembly remain |
| Universal corrected theorem | absent | Root integration outside this lane; zero qualifying credit |

All names above lie in namespace XorMagic. B and D, reverse affine constants, translation rank/cardinality arguments, fibre-size connectivity and walk lifting are reused unchanged from r4a. The plain magic theorems include a bijection to Bits (n+2); this is stronger than just an order count but does not by itself transport every seed field to that vertex type.

H1: inherited StrongFactorCycleData lower bound is carried into every persisted cycle. H2: proper colouring orients both factors globally; the indexed and actual walk directions are certified. H3: the exact inherited ordered incidence edge set is used; no independent B/D orientation is introduced. H4: lifted graph factors and indexed simple cycle persist; complement coverage/count is assumed via LiftComplementInput and remains r4b's duty. H5 and H7: interpolation and induction are not claimed here. H6: inherited direct finite base certificates remain byte-identical.
