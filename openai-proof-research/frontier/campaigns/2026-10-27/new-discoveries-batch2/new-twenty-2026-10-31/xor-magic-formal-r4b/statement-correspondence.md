# Statement correspondence

| Requested component | Lean declaration | Exact meaning |
| --- | --- | --- |
| Three internal factors | fibreMatching_involutive, fibreMatching_no_fixed, fibreMatching_distinct, fibreMatching_cover | Nonzero Four translations partition the internal K4 of every fibre. |
| Three missing factors per G factor | EdgeTransport.blockMate_nonzero_cover | Chart translations by nonzero Four elements cover precisely the edges over G absent from its transported matching. |
| Four factors per complement factor | blockMate_involutive, blockMate_distinct; EdgeTransport.complementMate_cover | All Four translations between endpoint charts cover the complete bipartite block. |
| Disjointness and exact coverage | EdgeTransport.complementMate_distinct, EdgeTransport.complementMate_cover | All three index families have distinct mates at every vertex and cover exactly the lift complement. |
| Inherited factor convention | EdgeTransport.complementMatching; EdgeTransport.complementMatching_exact | MatchingDecomposition with Fin (3+3*d+4*c), or Fin (card (V × Four)-1-d), fixed point free involutions and exact coverage. |
| Interpolation graph | EdgeTransport.interpGraph, EdgeTransport.interpMate | G factors with index below k use all nonzero chart translations; other G factors use zero translation; the first j complement factors use all four. |
| Simplicity and degree | involutionGraph; EdgeTransport.interpGraph_regular | A SimpleGraph, regular of degree d+2*k+4*j for k≤d and j≤c. |
| Sum preservation | EdgeTransport.interpGraph_sum, EdgeTransport.interp_label_sum | Every neighbourhood sum agrees with that in the original lift. General targets are abelian groups of exponent two with zero fibre sums. |
| Fibre cancellation | label_fibre_zero | The actual inherited product label sums to zero over every fibre, for all n including n=0. |
| Connectivity | EdgeTransport.interpGraph_connected | Connected base and connected lift imply connected interpolation, including k=0 and k>0. No replaced edge is presumed retained. |
| Magic types | EdgeTransport.interp_open, EdgeTransport.interp_closed | The lift's zero open/closed sums under label l imply literal OpenMagic/ClosedMagic after interpolation. |
| Literal intervals | interp_open_interval, interp_closed_interval | Every degree q of the given parity in [d,4*m-4-d] has bounded k,j and equality q=d+2*k+4*j. |
| Direct existence assembly | EdgeTransport.open_interval_exists, EdgeTransport.closed_interval_exists | Literal OpenExists/ClosedExists (n+2) q throughout the parity interval, with the inherited product label and explicit lift hypotheses. |

All new results are independent of the chosen scalar assignment and translations: EdgeTransport already abstracts every affine lift from r3. An ordering is used only to choose lower and upper endpoint charts. The zero chart translation is proved to be precisely the designated transport in matchingChart_transport and blockMate_zero. No r4a files are used.
