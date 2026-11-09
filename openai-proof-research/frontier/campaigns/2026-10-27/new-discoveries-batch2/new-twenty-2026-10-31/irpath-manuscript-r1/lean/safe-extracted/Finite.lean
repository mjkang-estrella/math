import Four
import Three
namespace IR350452
lemma walk_card (i : Fin 9) : (walk i).card = 3 := by
  revert i; decide

lemma walk_injective : Function.Injective walk := by
  intro i j h
  revert i j
  decide


end IR350452
