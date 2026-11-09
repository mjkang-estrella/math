import ChainPrefix
namespace ChainPrefix
def all3 (p : V → V → V → Bool) : Bool := (List.finRange 11).all fun b =>
  (List.finRange 11).all fun c => (List.finRange 11).all fun m => p b c m
theorem all3_sound {p} (h : all3 p = true) (b c m : V) : p b c m = true := by
  exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h b (by simp)) c (by simp)) m (by simp)
def all2 (p : V → V → Bool) : Bool := (List.finRange 11).all fun c => (List.finRange 11).all fun m => p c m
theorem all2_sound {p} (h : all2 p = true) (c m : V) : p c m = true := by
  exact List.all_eq_true.mp (List.all_eq_true.mp h c (by simp)) m (by simp)
end ChainPrefix
