import Definitions
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Cayley
theorem total_five : ((allWords 5 5).filter packedB).length = 541 := by decide
theorem total_five_card : (wordUniverse 5).card = 541 := by
  rw [wordUniverse, List.toFinset_card_of_nodup ((nodup_allWords 5 5).filter packedB)]
  exact total_five
theorem avoid_p : (avoiders 5 [1,1,2,2]).card = 520 := by rw [card_eq_length]; decide
theorem avoid_q : (avoiders 5 [1,1,1,2]).card = 522 := by rw [card_eq_length]; decide
theorem packed_p : Packed [1,1,2,2] := (packedB_iff _).mp (by decide)
theorem packed_q : Packed [1,1,1,2] := (packedB_iff _).mp (by decide)
theorem contain_p : ((wordUniverse 5).sdiff (avoiders 5 [1,1,2,2])).card = 21 := by
  rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), total_five_card, avoid_p]
theorem contain_q : ((wordUniverse 5).sdiff (avoiders 5 [1,1,1,2])).card = 19 := by
  rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), total_five_card, avoid_q]
theorem literal_source_claim_false : ¬ SourceClaim := by
  intro h
  have hc := h [1,1,2,2] [1,1,1,2] packed_p packed_q rfl (by decide) 5
  rw [sourceCount_eq, sourceCount_eq, avoid_p, avoid_q] at hc
  omega
end Cayley
