import Closure5C000
import Closure5C001
import Closure5C002
import Closure5C003
import Closure5C004
import Closure5C005
import Closure5C006
import Closure5C007
set_option autoImplicit false
namespace Polyomino57
def closedLayer5 : Array (List GridPoint) := (Closure5C000rows ++ (Closure5C001rows ++ (Closure5C002rows ++ (Closure5C003rows ++ (Closure5C004rows ++ (Closure5C005rows ++ (Closure5C006rows ++ (Closure5C007rows)))))))).toArray
theorem closure5_local : LocallyClosed closedLayer5 layer6 := by
  intro row hr
  simp only [closedLayer5,List.toList_toArray,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact Closure5C000_closed row h0
  · exact Closure5C001_closed row h1
  · exact Closure5C002_closed row h2
  · exact Closure5C003_closed row h3
  · exact Closure5C004_closed row h4
  · exact Closure5C005_closed row h5
  · exact Closure5C006_closed row h6
  · exact Closure5C007_closed row h7
theorem closure5 : ∃ choices, arrayClosureCheck closedLayer5 layer6 choices = true :=
  locallyClosed_array closure5_local
end Polyomino57
