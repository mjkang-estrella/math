import ChainFirst3_2
import ChainFirst3_6
import ChainFirst6_3
import ChainFirst6_4
namespace ChainPrefix
theorem first3 (l b c m : V) (hf : Fits (first 3 b c l m)) :
    ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧
    ((l = 2 ∧ m = 6) ∨ (l = 6 ∧ m = 2)) := by
  have ha := attachments3 l m (fits_attachments _ _ _ _ _ hf)
  refine ⟨?_,ha⟩
  rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact first3_2 b c hf
  · exact first3_6 b c hf
 theorem first6 (l b c m : V) (hf : Fits (first 6 b c l m)) :
    ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧
    ((l = 3 ∧ m = 4) ∨ (l = 4 ∧ m = 3)) := by
  have ha := attachments6 l m (fits_attachments _ _ _ _ _ hf)
  refine ⟨?_,ha⟩
  rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact first6_3 b c hf
  · exact first6_4 b c hf
end ChainPrefix
