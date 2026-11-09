import Foundation
set_option autoImplicit false
namespace WheelReview
/-- Twice source Lemma 4.2, applied after swapping coordinates,
    implies the entire new dual inequality by addition. -/
theorem source_lemma42_implies_weight_bound (t a b n : ℝ)
    (ha : n ≤ t*(2*t+1)+1+(1-t)*a)
    (hb : n ≤ t*(2*t+1)+1+(1-t)*b) :
    2*n+(t-1)*(a+b) ≤ 2*(2*t^2+t+1) := by
  nlinarith
end WheelReview
#print axioms WheelReview.source_lemma42_implies_weight_bound
