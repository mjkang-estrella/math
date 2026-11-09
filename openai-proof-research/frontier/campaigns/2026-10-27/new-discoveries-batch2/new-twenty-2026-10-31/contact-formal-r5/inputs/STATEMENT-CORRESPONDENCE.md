# Statement correspondence

All inherited source statements and definitions are byte-identical; see inputs/before.json and inputs/after.json. The inherited correspondence is copied at inputs/STATEMENT-CORRESPONDENCE.md.

| Declaration | Exact role | Status |
| --- | --- | --- |
| `bidisk_denominator_stable` | ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → eval₂ bidiskDenominator z w ≠ 0 | Unconditional |
| `bidisk_represents_graph` | beta of the actual candidate graph resolvent at betaInv coordinates equals the inherited bidisk numerator/denominator quotient on the entire open bidisk | Unconditional |
| `bidisk_denominator_bounds` | ∀ d ∈ bidiskDenominator.support, d 0 ≤ 3 ∧ d 1 ≤ 2 | Unconditional |
| `bidisk_reflection` | ∀ z w, eval₂ bidiskNumerator z w = (1 : ℂ) * reflect bidiskDenominator 3 2 z w | Unconditional |
| `candidateCertificate` | ReducedCertificate (graphFunction candidateGraph candidateColors 0), numerator = bidiskNumerator, denominator = bidiskDenominator, degreeZ = 3, degreeW = 2, phase = 1 | Constructed |
| `half_plane_contact_six` | HasHalfPlaneContact R 6 | Inherited |
| `bidisk_contact_six` | HasZeroSetContact (eval₂ bidiskNumerator) (-1) 1 6 | Missing |
| `refutation_of_bidisk_contact` | HasZeroSetContact (eval₂ bidiskNumerator) (-1) 1 6 → ¬ SourceConjecture | Conditional only |
| `ContactPilot.refutation` | ¬ ContactPilot.SourceConjecture | Missing; zero credit |

No modification of SourceConjecture, HasZeroSetContact, HasHalfPlaneContact, graphFunction, reflect or the assigned polynomials is used. The finite graph, root, colors and nearest-w distance are inherited. No new-to-literature conclusion follows from this partial formalization.
