import BidiskReflection
namespace ContactPilot
noncomputable section

/-- Unconditional certificate for the actual graph resolvent, with the
inherited cleared polynomials and the literal coefficient reflection. -/
def candidateCertificate : ReducedCertificate (graphFunction candidateGraph candidateColors 0) where
  numerator := bidiskNumerator
  denominator := bidiskDenominator
  denominator_ne := bidiskDenominator_ne_zero
  reduced := bidisk_pair_reduced
  stable := bidisk_denominator_stable
  represents := bidisk_represents_graph
  degreeZ := 3
  degreeW := 2
  bounds := bidisk_denominator_bounds
  phase := 1
  phase_norm := norm_one
  reflection := bidisk_reflection

/-- This explicitly conditional implication is not the requested refutation. -/
theorem refutation_of_bidisk_contact
    (hc : HasZeroSetContact (eval₂ bidiskNumerator) (-1) 1 6) : ¬ SourceConjecture := by
  intro h
  have he := h 5 candidateGraph candidateColors 0 candidateCertificate 1 6
    nearest_w_one (by norm_num) (by norm_num) hc
  norm_num at he

end
end ContactPilot
