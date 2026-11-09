import SupportData156
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport156
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0230.C7368, NewCertificates0230.C7369, NewCertificates0230.C7370, NewCertificates0230.C7371, NewCertificates0230.C7372, NewCertificates0230.C7373, NewCertificates0230.C7374, NewCertificates0230.C7375, NewCertificates0230.C7376, NewCertificates0230.C7377, NewCertificates0230.C7378, NewCertificates0230.C7379, NewCertificates0230.C7380, NewCertificates0230.C7381, NewCertificates0230.C7382, NewCertificates0230.C7383, NewCertificates0230.C7384, NewCertificates0230.C7385, NewCertificates0230.C7386, NewCertificates0230.C7387, NewCertificates0230.C7388, NewCertificates0230.C7389, NewCertificates0230.C7390, NewCertificates0230.C7391, NewCertificates0231.C7392, NewCertificates0231.C7393, NewCertificates0231.C7394, NewCertificates0231.C7395, NewCertificates0231.C7396, NewCertificates0231.C7397, NewCertificates0231.C7398, NewCertificates0231.C7399} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0230.obstruction7368
  · exact NewCertificates0230.obstruction7369
  · exact NewCertificates0230.obstruction7370
  · exact NewCertificates0230.obstruction7371
  · exact NewCertificates0230.obstruction7372
  · exact NewCertificates0230.obstruction7373
  · exact NewCertificates0230.obstruction7374
  · exact NewCertificates0230.obstruction7375
  · exact NewCertificates0230.obstruction7376
  · exact NewCertificates0230.obstruction7377
  · exact NewCertificates0230.obstruction7378
  · exact NewCertificates0230.obstruction7379
  · exact NewCertificates0230.obstruction7380
  · exact NewCertificates0230.obstruction7381
  · exact NewCertificates0230.obstruction7382
  · exact NewCertificates0230.obstruction7383
  · exact NewCertificates0230.obstruction7384
  · exact NewCertificates0230.obstruction7385
  · exact NewCertificates0230.obstruction7386
  · exact NewCertificates0230.obstruction7387
  · exact NewCertificates0230.obstruction7388
  · exact NewCertificates0230.obstruction7389
  · exact NewCertificates0230.obstruction7390
  · exact NewCertificates0230.obstruction7391
  · exact NewCertificates0231.obstruction7392
  · exact NewCertificates0231.obstruction7393
  · exact NewCertificates0231.obstruction7394
  · exact NewCertificates0231.obstruction7395
  · exact NewCertificates0231.obstruction7396
  · exact NewCertificates0231.obstruction7397
  · exact NewCertificates0231.obstruction7398
  · exact NewCertificates0231.obstruction7399
end Nut8.FiniteSupport156
