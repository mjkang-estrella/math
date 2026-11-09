import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_680 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]
def row7_680choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2370,(1,0))),((0,1),(1402,(0,0))),((0,3),(2012,(0,0))),((1,0),(2178,(0,0))),((1,1),(2217,(0,0))),((1,3),(2274,(0,0))),((2,-1),(2604,(0,1))),((2,3),(2304,(0,0))),((3,0),(2311,(0,0))),((3,2),(2318,(0,0))),((4,0),(2320,(0,0))),((4,2),(2321,(0,0))),((5,1),(2322,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_680_checked : successorFastRowCheck layer8 row7_680 row7_680choice = true := by decide
def row7_681 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)]
def row7_681choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2371,(1,0))),((0,1),(1403,(0,0))),((0,3),(2013,(0,0))),((1,0),(2179,(0,0))),((1,1),(2218,(0,0))),((1,3),(2275,(0,0))),((2,-1),(2605,(0,1))),((2,3),(2305,(0,0))),((3,0),(2312,(0,0))),((3,1),(2317,(0,0))),((3,4),(2323,(0,0))),((4,2),(2324,(0,0))),((4,3),(2325,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_681_checked : successorFastRowCheck layer8 row7_681 row7_681choice = true := by decide
def row7_682 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]
def row7_682choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2372,(1,0))),((0,1),(1404,(0,0))),((0,3),(2014,(0,0))),((1,0),(2180,(0,0))),((1,1),(2219,(0,0))),((1,3),(2276,(0,0))),((2,-1),(2606,(0,1))),((2,3),(2306,(0,0))),((3,0),(2314,(0,0))),((3,1),(2319,(0,0))),((3,3),(2324,(0,0))),((4,1),(2326,(0,0))),((4,3),(2327,(0,0))),((5,2),(2328,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_682_checked : successorFastRowCheck layer8 row7_682 row7_682choice = true := by decide
def row7_683 : List GridPoint := [(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)]
def row7_683choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2373,(1,0))),((0,1),(1405,(0,0))),((0,3),(2015,(0,0))),((1,0),(2181,(0,0))),((1,1),(2231,(0,0))),((1,3),(2277,(0,0))),((2,-1),(2607,(0,1))),((2,1),(2309,(0,0))),((2,3),(2329,(0,0))),((3,-1),(2616,(0,1))),((3,3),(2330,(0,0))),((4,0),(2331,(0,0))),((4,1),(2332,(0,0))),((4,2),(2333,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_683_checked : successorFastRowCheck layer8 row7_683 row7_683choice = true := by decide
def row7_684 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)]
def row7_684choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2374,(1,0))),((0,1),(1406,(0,0))),((0,3),(2016,(0,0))),((1,1),(2232,(0,0))),((1,3),(2278,(0,0))),((2,0),(2298,(0,0))),((2,4),(2334,(0,0))),((3,-1),(2617,(0,1))),((3,2),(2335,(0,0))),((3,3),(2336,(0,0))),((4,0),(2337,(0,0))),((4,1),(2338,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_684_checked : successorFastRowCheck layer8 row7_684 row7_684choice = true := by decide
def row7_685 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)]
def row7_685choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2375,(1,0))),((0,1),(1407,(0,0))),((0,3),(2017,(0,0))),((1,1),(2233,(0,0))),((1,3),(2279,(0,0))),((2,0),(2309,(0,0))),((2,3),(2335,(0,0))),((3,-1),(2618,(0,1))),((3,3),(2340,(0,0))),((4,0),(2341,(0,0))),((4,1),(2342,(0,0))),((4,2),(2343,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_685_checked : successorFastRowCheck layer8 row7_685 row7_685choice = true := by decide
def row7_686 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)]
def row7_686choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2376,(1,0))),((0,1),(1408,(0,0))),((0,3),(2018,(0,0))),((1,1),(2234,(0,0))),((1,3),(2280,(0,0))),((2,0),(2310,(0,0))),((2,3),(2337,(0,0))),((3,-1),(2620,(0,1))),((3,2),(2341,(0,0))),((4,-1),(2622,(0,1))),((4,1),(2344,(0,0))),((5,0),(2345,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_686_checked : successorFastRowCheck layer8 row7_686 row7_686choice = true := by decide
def row7_687 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]
def row7_687choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2377,(1,0))),((0,1),(1409,(0,0))),((0,3),(2019,(0,0))),((1,1),(2235,(0,0))),((1,3),(2281,(0,0))),((2,0),(2311,(0,0))),((2,3),(2338,(0,0))),((3,-1),(2621,(0,1))),((3,2),(2342,(0,0))),((4,0),(2344,(0,0))),((4,2),(2346,(0,0))),((5,1),(2347,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_687_checked : successorFastRowCheck layer8 row7_687 row7_687choice = true := by decide
def Closure7C085rows : List (List GridPoint) := [row7_680,row7_681,row7_682,row7_683,row7_684,row7_685,row7_686,row7_687]
theorem Closure7C085_closed : ∀ row ∈ Closure7C085rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C085rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_680choice,row7_680_checked⟩
  · subst row
    exact ⟨row7_681choice,row7_681_checked⟩
  · subst row
    exact ⟨row7_682choice,row7_682_checked⟩
  · subst row
    exact ⟨row7_683choice,row7_683_checked⟩
  · subst row
    exact ⟨row7_684choice,row7_684_checked⟩
  · subst row
    exact ⟨row7_685choice,row7_685_checked⟩
  · subst row
    exact ⟨row7_686choice,row7_686_checked⟩
  · subst row
    exact ⟨row7_687choice,row7_687_checked⟩
end Polyomino57
