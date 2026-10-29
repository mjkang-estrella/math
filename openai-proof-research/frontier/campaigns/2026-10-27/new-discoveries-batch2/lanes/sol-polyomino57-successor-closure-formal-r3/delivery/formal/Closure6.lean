import Closure6C000
import Closure6C001
import Closure6C002
import Closure6C003
import Closure6C004
import Closure6C005
import Closure6C006
import Closure6C007
import Closure6C008
import Closure6C009
import Closure6C010
import Closure6C011
import Closure6C012
import Closure6C013
import Closure6C014
import Closure6C015
import Closure6C016
import Closure6C017
import Closure6C018
import Closure6C019
import Closure6C020
import Closure6C021
import Closure6C022
import Closure6C023
import Closure6C024
import Closure6C025
import Closure6C026
set_option autoImplicit false
namespace Polyomino57
def closedLayer6 : Array (List GridPoint) := (Closure6C000rows ++ (Closure6C001rows ++ (Closure6C002rows ++ (Closure6C003rows ++ (Closure6C004rows ++ (Closure6C005rows ++ (Closure6C006rows ++ (Closure6C007rows ++ (Closure6C008rows ++ (Closure6C009rows ++ (Closure6C010rows ++ (Closure6C011rows ++ (Closure6C012rows ++ (Closure6C013rows ++ (Closure6C014rows ++ (Closure6C015rows ++ (Closure6C016rows ++ (Closure6C017rows ++ (Closure6C018rows ++ (Closure6C019rows ++ (Closure6C020rows ++ (Closure6C021rows ++ (Closure6C022rows ++ (Closure6C023rows ++ (Closure6C024rows ++ (Closure6C025rows ++ (Closure6C026rows))))))))))))))))))))))))))).toArray
theorem closure6_local : LocallyClosed closedLayer6 layer7 := by
  intro row hr
  simp only [closedLayer6,List.toList_toArray,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26
  · exact Closure6C000_closed row h0
  · exact Closure6C001_closed row h1
  · exact Closure6C002_closed row h2
  · exact Closure6C003_closed row h3
  · exact Closure6C004_closed row h4
  · exact Closure6C005_closed row h5
  · exact Closure6C006_closed row h6
  · exact Closure6C007_closed row h7
  · exact Closure6C008_closed row h8
  · exact Closure6C009_closed row h9
  · exact Closure6C010_closed row h10
  · exact Closure6C011_closed row h11
  · exact Closure6C012_closed row h12
  · exact Closure6C013_closed row h13
  · exact Closure6C014_closed row h14
  · exact Closure6C015_closed row h15
  · exact Closure6C016_closed row h16
  · exact Closure6C017_closed row h17
  · exact Closure6C018_closed row h18
  · exact Closure6C019_closed row h19
  · exact Closure6C020_closed row h20
  · exact Closure6C021_closed row h21
  · exact Closure6C022_closed row h22
  · exact Closure6C023_closed row h23
  · exact Closure6C024_closed row h24
  · exact Closure6C025_closed row h25
  · exact Closure6C026_closed row h26
theorem closure6 : ∃ choices, arrayClosureCheck closedLayer6 layer7 choices = true :=
  locallyClosed_array closure6_local
end Polyomino57
