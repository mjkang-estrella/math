import CountR7TFinal
namespace ChanLevine.Round7T.Controls
open ChanLevine.Round6
open ChanLevine.Round7T

def wrapWord : StateWord 4 := fun k => if k = 0 then 1 else 0

theorem wrap_selected : selected wrapWord = {3} := by decide

theorem wrap_admissible : Admissible wrapWord := by unfold Admissible; decide

theorem even_alternating_a : selected (fun k : ZMod 4 => if k.val % 2 = 1 then 1 else 0) =
    {0,2} := by decide

theorem even_alternating_b : selected (fun k : ZMod 4 => if k.val % 2 = 0 then 1 else 0) =
    {1,3} := by decide

theorem wrong_sign_rejected :
    wordWeight (2 : ℤ) (fun _ : ZMod 4 => 1) wrapWord = -18 := by decide
end ChanLevine.Round7T.Controls
