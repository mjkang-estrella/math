import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_592 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)]
def row7_592choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2282,(1,0))),((-1,3),(2572,(1,0))),((0,1),(1221,(0,0))),((0,4),(1921,(0,0))),((1,0),(1959,(0,0))),((1,3),(1980,(0,0))),((2,0),(1985,(0,0))),((2,2),(1989,(0,0))),((3,-1),(2429,(0,1))),((3,2),(1990,(0,0))),((4,0),(1991,(0,0))),((4,1),(1992,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_592_checked : successorFastRowCheck layer8 row7_592 row7_592choice = true := by decide
def row7_593 : List GridPoint := [(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row7_593choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2283,(1,0))),((-1,3),(2573,(1,0))),((0,1),(1241,(0,0))),((0,4),(1922,(0,0))),((1,0),(1969,(0,0))),((1,1),(1976,(0,0))),((1,4),(1996,(0,0))),((2,-1),(2430,(0,1))),((2,3),(1997,(0,0))),((3,0),(1998,(0,0))),((3,1),(1999,(0,0))),((3,2),(2000,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_593_checked : successorFastRowCheck layer8 row7_593 row7_593choice = true := by decide
def row7_594 : List GridPoint := [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)]
def row7_594choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2284,(1,0))),((-1,3),(2574,(1,0))),((0,1),(1242,(0,0))),((0,4),(1924,(0,0))),((1,0),(1970,(0,0))),((1,1),(1981,(0,0))),((1,3),(1997,(0,0))),((2,-1),(2431,(0,1))),((2,4),(2003,(0,0))),((3,0),(2004,(0,0))),((3,1),(2005,(0,0))),((3,2),(2006,(0,0))),((3,3),(2007,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_594_checked : successorFastRowCheck layer8 row7_594 row7_594choice = true := by decide
def row7_595 : List GridPoint := [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)]
def row7_595choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2285,(1,0))),((-1,3),(2575,(1,0))),((0,1),(1243,(0,0))),((0,4),(1925,(0,0))),((1,0),(1971,(0,0))),((1,1),(1982,(0,0))),((1,3),(1998,(0,0))),((2,-1),(2433,(0,1))),((2,3),(2004,(0,0))),((3,-1),(2436,(0,1))),((3,1),(2008,(0,0))),((3,2),(2009,(0,0))),((4,0),(2010,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_595_checked : successorFastRowCheck layer8 row7_595 row7_595choice = true := by decide
def row7_596 : List GridPoint := [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)]
def row7_596choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2286,(1,0))),((-1,3),(2576,(1,0))),((0,1),(1244,(0,0))),((0,4),(1926,(0,0))),((1,0),(1972,(0,0))),((1,1),(1983,(0,0))),((1,3),(1999,(0,0))),((2,-1),(2434,(0,1))),((2,3),(2005,(0,0))),((3,0),(2008,(0,0))),((3,2),(2011,(0,0))),((4,1),(2012,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_596_checked : successorFastRowCheck layer8 row7_596 row7_596choice = true := by decide
def row7_597 : List GridPoint := [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)]
def row7_597choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2287,(1,0))),((-1,3),(2577,(1,0))),((0,1),(1245,(0,0))),((0,4),(1927,(0,0))),((1,0),(1973,(0,0))),((1,1),(1984,(0,0))),((1,3),(2000,(0,0))),((2,-1),(2435,(0,1))),((2,3),(2006,(0,0))),((3,0),(2009,(0,0))),((3,1),(2011,(0,0))),((3,3),(2013,(0,0))),((4,2),(2014,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_597_checked : successorFastRowCheck layer8 row7_597 row7_597choice = true := by decide
def row7_598 : List GridPoint := [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)]
def row7_598choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2288,(1,0))),((-1,3),(2578,(1,0))),((0,1),(1246,(0,0))),((0,4),(1928,(0,0))),((1,1),(1989,(0,0))),((1,3),(2001,(0,0))),((2,0),(2008,(0,0))),((2,3),(2016,(0,0))),((3,-1),(2437,(0,1))),((3,2),(2017,(0,0))),((4,0),(2018,(0,0))),((4,1),(2019,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_598_checked : successorFastRowCheck layer8 row7_598 row7_598choice = true := by decide
def row7_599 : List GridPoint := [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)]
def row7_599choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2289,(1,0))),((-1,3),(2579,(1,0))),((0,1),(1247,(0,0))),((0,4),(1929,(0,0))),((1,1),(1994,(0,0))),((1,3),(2002,(0,0))),((2,0),(2015,(0,0))),((2,1),(2017,(0,0))),((2,3),(2021,(0,0))),((3,-1),(2438,(0,1))),((3,3),(2022,(0,0))),((4,0),(2023,(0,0))),((4,1),(2024,(0,0))),((4,2),(2025,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_599_checked : successorFastRowCheck layer8 row7_599 row7_599choice = true := by decide
def Closure7C074rows : List (List GridPoint) := [row7_592,row7_593,row7_594,row7_595,row7_596,row7_597,row7_598,row7_599]
theorem Closure7C074_closed : ∀ row ∈ Closure7C074rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C074rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_592choice,row7_592_checked⟩
  · subst row
    exact ⟨row7_593choice,row7_593_checked⟩
  · subst row
    exact ⟨row7_594choice,row7_594_checked⟩
  · subst row
    exact ⟨row7_595choice,row7_595_checked⟩
  · subst row
    exact ⟨row7_596choice,row7_596_checked⟩
  · subst row
    exact ⟨row7_597choice,row7_597_checked⟩
  · subst row
    exact ⟨row7_598choice,row7_598_checked⟩
  · subst row
    exact ⟨row7_599choice,row7_599_checked⟩
end Polyomino57
