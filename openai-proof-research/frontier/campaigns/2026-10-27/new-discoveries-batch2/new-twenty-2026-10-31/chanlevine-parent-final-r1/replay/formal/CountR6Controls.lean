import CountFinal5
import CountR5Controls
namespace ChanLevine.Round6.Controls
open Round6

theorem wrap_matching : Matching ({3} : Finset (ZMod 4)) := by
  unfold Matching
  decide

theorem wrap_endpoints : ({3} ∪ rightEnds ({3} : Finset (ZMod 4))) = {3,0} := by
  unfold rightEnds
  decide

theorem alternating_even : Matching ({0,2} : Finset (ZMod 4)) := by
  unfold Matching
  decide

theorem alternating_odd : Matching ({1,3} : Finset (ZMod 4)) := by
  unfold Matching
  decide

theorem adjacent_rejected : ¬ Matching ({0,1} : Finset (ZMod 4)) := by
  unfold Matching
  decide
end ChanLevine.Round6.Controls
