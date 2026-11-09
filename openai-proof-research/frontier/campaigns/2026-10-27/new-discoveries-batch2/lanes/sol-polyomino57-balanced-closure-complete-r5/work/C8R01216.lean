import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01216G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1216_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)] := by
    let c8r1216targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1216choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1216targets [(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)] c8r1216choice = true := by decide
    refine ⟨c8r1216targets, c8r1216choice, ?_, checked⟩
    intro S h
    simp only [c8r1216targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 29 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L11_lift _ (familyLookup_sound F9B003L11 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 5 _ (by rfl)))
  have c8r1217_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r1217targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r1217choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1217targets [(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)] c8r1217choice = true := by decide
    refine ⟨c8r1217targets, c8r1217choice, ?_, checked⟩
    intro S h
    simp only [c8r1217targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 30 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 11 _ (by rfl)))
  have c8r1218_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)] := by
    let c8r1218targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1218choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1218targets [(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)] c8r1218choice = true := by decide
    refine ⟨c8r1218targets, c8r1218choice, ?_, checked⟩
    intro S h
    simp only [c8r1218targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L44_lift _ (familyLookup_sound F9B003L44 [] 31 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 16 _ (by rfl)))
  have c8r1219_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)] := by
    let c8r1219targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
    let c8r1219choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1219targets [(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)] c8r1219choice = true := by decide
    refine ⟨c8r1219targets, c8r1219choice, ?_, checked⟩
    intro S h
    simp only [c8r1219targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 0 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 18 _ (by rfl)))
  have c8r1220_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)] := by
    let c8r1220targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
    let c8r1220choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1220targets [(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)] c8r1220choice = true := by decide
    refine ⟨c8r1220targets, c8r1220choice, ?_, checked⟩
    intro S h
    simp only [c8r1220targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 1 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 20 _ (by rfl)))
  have c8r1221_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)] := by
    let c8r1221targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1221choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1221targets [(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)] c8r1221choice = true := by decide
    refine ⟨c8r1221targets, c8r1221choice, ?_, checked⟩
    intro S h
    simp only [c8r1221targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 2 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L21_lift _ (familyLookup_sound F9B004L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 24 _ (by rfl)))
  have c8r1222_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1)] := by
    let c8r1222targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c8r1222choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1222targets [(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1)] c8r1222choice = true := by decide
    refine ⟨c8r1222targets, c8r1222choice, ?_, checked⟩
    intro S h
    simp only [c8r1222targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 3 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 0 _ (by rfl)))
  have c8r1223_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r1223targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1223choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1223targets [(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2)] c8r1223choice = true := by decide
    refine ⟨c8r1223targets, c8r1223choice, ?_, checked⟩
    intro S h
    simp only [c8r1223targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 4 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 5 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1216_closed
  · subst row; exact c8r1217_closed
  · subst row; exact c8r1218_closed
  · subst row; exact c8r1219_closed
  · subst row; exact c8r1220_closed
  · subst row; exact c8r1221_closed
  · subst row; exact c8r1222_closed
  · subst row; exact c8r1223_closed
theorem C8R01216G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1224_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3)] := by
    let c8r1224targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,3)]]
    let c8r1224choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1224targets [(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3)] c8r1224choice = true := by decide
    refine ⟨c8r1224targets, c8r1224choice, ?_, checked⟩
    intro S h
    simp only [c8r1224targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 5 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L12_lift _ (familyLookup_sound F9B003L12 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 9 _ (by rfl)))
  have c8r1225_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0)] := by
    let c8r1225targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(4,0)]]
    let c8r1225choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1225targets [(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0)] c8r1225choice = true := by decide
    refine ⟨c8r1225targets, c8r1225choice, ?_, checked⟩
    intro S h
    simp only [c8r1225targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 6 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 11 _ (by rfl)))
  have c8r1226_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1)] := by
    let c8r1226targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(4,1)]]
    let c8r1226choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1226targets [(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1)] c8r1226choice = true := by decide
    refine ⟨c8r1226targets, c8r1226choice, ?_, checked⟩
    intro S h
    simp only [c8r1226targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 13 _ (by rfl)))
  have c8r1227_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1)] := by
    let c8r1227targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1227choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,2),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1227targets [(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1)] c8r1227choice = true := by decide
    refine ⟨c8r1227targets, c8r1227choice, ?_, checked⟩
    intro S h
    simp only [c8r1227targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L61_lift _ (familyLookup_sound F9B001L61 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 18 _ (by rfl)))
  have c8r1228_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1228targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1228choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1228targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3)] c8r1228choice = true := by decide
    refine ⟨c8r1228targets, c8r1228choice, ?_, checked⟩
    intro S h
    simp only [c8r1228targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 9 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 24 _ (by rfl)))
  have c8r1229_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r1229targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r1229choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1229targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0)] c8r1229choice = true := by decide
    refine ⟨c8r1229targets, c8r1229choice, ?_, checked⟩
    intro S h
    simp only [c8r1229targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 10 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 27 _ (by rfl)))
  have c8r1230_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r1230targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1230choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1230targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)] c8r1230choice = true := by decide
    refine ⟨c8r1230targets, c8r1230choice, ?_, checked⟩
    intro S h
    simp only [c8r1230targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 11 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 29 _ (by rfl)))
  have c8r1231_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r1231targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1231choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1231targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2)] c8r1231choice = true := by decide
    refine ⟨c8r1231targets, c8r1231choice, ?_, checked⟩
    intro S h
    simp only [c8r1231targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 12 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 31 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1224_closed
  · subst row; exact c8r1225_closed
  · subst row; exact c8r1226_closed
  · subst row; exact c8r1227_closed
  · subst row; exact c8r1228_closed
  · subst row; exact c8r1229_closed
  · subst row; exact c8r1230_closed
  · subst row; exact c8r1231_closed
theorem C8R01216G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1232_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)] := by
    let c8r1232targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1232choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1232targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)] c8r1232choice = true := by decide
    refine ⟨c8r1232targets, c8r1232choice, ?_, checked⟩
    intro S h
    simp only [c8r1232targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 13 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 2 _ (by rfl)))
  have c8r1233_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0)] := by
    let c8r1233targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c8r1233choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1233targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0)] c8r1233choice = true := by decide
    refine ⟨c8r1233targets, c8r1233choice, ?_, checked⟩
    intro S h
    simp only [c8r1233targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 4 _ (by rfl)))
  have c8r1234_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2)] := by
    let c8r1234targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c8r1234choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1234targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2)] c8r1234choice = true := by decide
    refine ⟨c8r1234targets, c8r1234choice, ?_, checked⟩
    intro S h
    simp only [c8r1234targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 15 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 7 _ (by rfl)))
  have c8r1235_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1)] := by
    let c8r1235targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c8r1235choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1235targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1)] c8r1235choice = true := by decide
    refine ⟨c8r1235targets, c8r1235choice, ?_, checked⟩
    intro S h
    simp only [c8r1235targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 16 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 10 _ (by rfl)))
  have c8r1236_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r1236targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r1236choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1236targets [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1)] c8r1236choice = true := by decide
    refine ⟨c8r1236targets, c8r1236choice, ?_, checked⟩
    intro S h
    simp only [c8r1236targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 17 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L58_lift _ (familyLookup_sound F9B001L58 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 14 _ (by rfl)))
  have c8r1237_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r1237targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1237choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1237targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2)] c8r1237choice = true := by decide
    refine ⟨c8r1237targets, c8r1237choice, ?_, checked⟩
    intro S h
    simp only [c8r1237targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 18 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 19 _ (by rfl)))
  have c8r1238_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r1238targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r1238choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1238targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0)] c8r1238choice = true := by decide
    refine ⟨c8r1238targets, c8r1238choice, ?_, checked⟩
    intro S h
    simp only [c8r1238targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 19 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 21 _ (by rfl)))
  have c8r1239_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r1239targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r1239choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1239targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1)] c8r1239choice = true := by decide
    refine ⟨c8r1239targets, c8r1239choice, ?_, checked⟩
    intro S h
    simp only [c8r1239targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 20 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 23 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1232_closed
  · subst row; exact c8r1233_closed
  · subst row; exact c8r1234_closed
  · subst row; exact c8r1235_closed
  · subst row; exact c8r1236_closed
  · subst row; exact c8r1237_closed
  · subst row; exact c8r1238_closed
  · subst row; exact c8r1239_closed
theorem C8R01216G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1240_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r1240targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r1240choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,-1),(12,(0,1))),((4,2),(13,(0,0))),((5,0),(14,(0,0))),((5,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1240targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1)] c8r1240choice = true := by decide
    refine ⟨c8r1240targets, c8r1240choice, ?_, checked⟩
    intro S h
    simp only [c8r1240targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 21 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L62_lift _ (familyLookup_sound F9B001L62 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L0_lift _ (familyLookup_sound F9B002L0 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 27 _ (by rfl)))
  have c8r1241_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r1241targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1241choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1241targets [(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r1241choice = true := by decide
    refine ⟨c8r1241targets, c8r1241choice, ?_, checked⟩
    intro S h
    simp only [c8r1241targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 22 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 1 _ (by rfl)))
  have c8r1242_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1242targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1242choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1242targets [(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)] c8r1242choice = true := by decide
    refine ⟨c8r1242targets, c8r1242choice, ?_, checked⟩
    intro S h
    simp only [c8r1242targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 23 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L13_lift _ (familyLookup_sound F9B003L13 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 8 _ (by rfl)))
  have c8r1243_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r1243targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r1243choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1243targets [(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)] c8r1243choice = true := by decide
    refine ⟨c8r1243targets, c8r1243choice, ?_, checked⟩
    intro S h
    simp only [c8r1243targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 24 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L1_lift _ (familyLookup_sound F9B002L1 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 11 _ (by rfl)))
  have c8r1244_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r1244targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1244choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1244targets [(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)] c8r1244choice = true := by decide
    refine ⟨c8r1244targets, c8r1244choice, ?_, checked⟩
    intro S h
    simp only [c8r1244targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 25 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 13 _ (by rfl)))
  have c8r1245_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r1245targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1245choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1245targets [(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)] c8r1245choice = true := by decide
    refine ⟨c8r1245targets, c8r1245choice, ?_, checked⟩
    intro S h
    simp only [c8r1245targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 26 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 15 _ (by rfl)))
  have c8r1246_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r1246targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r1246choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1246targets [(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)] c8r1246choice = true := by decide
    refine ⟨c8r1246targets, c8r1246choice, ?_, checked⟩
    intro S h
    simp only [c8r1246targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 20 _ (by rfl)))
  have c8r1247_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r1247targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1247choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1247targets [(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)] c8r1247choice = true := by decide
    refine ⟨c8r1247targets, c8r1247choice, ?_, checked⟩
    intro S h
    simp only [c8r1247targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L45_lift _ (familyLookup_sound F9B003L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L22_lift _ (familyLookup_sound F9B004L22 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L14_lift _ (familyLookup_sound F9B003L14 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L2_lift _ (familyLookup_sound F9B002L2 [] 26 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1240_closed
  · subst row; exact c8r1241_closed
  · subst row; exact c8r1242_closed
  · subst row; exact c8r1243_closed
  · subst row; exact c8r1244_closed
  · subst row; exact c8r1245_closed
  · subst row; exact c8r1246_closed
  · subst row; exact c8r1247_closed
theorem C8R01216_closed (row : List GridPoint) (h : FamilyMember row F8B000L38) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L38, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01216G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01216G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01216G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01216G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01216G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01216G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01216G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01216G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01216G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01216G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01216G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01216G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01216G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01216G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01216G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01216G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01216G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01216G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01216G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01216G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01216G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01216G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01216G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01216G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01216G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01216G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01216G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01216G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01216G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01216G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01216G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01216G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
