import Grid
set_option autoImplicit false
namespace Polyomino57

theorem connected_singleton (p : GridPoint) : EdgeConnected {p} := by
  refine ⟨Finset.singleton_nonempty p, ?_⟩
  intro a ha b hb
  have ha' := Finset.mem_singleton.mp ha
  have hb' := Finset.mem_singleton.mp hb
  subst a; subst b
  exact .refl

theorem connected_insert {Q : Finset GridPoint} {a b : GridPoint}
    (hQ : EdgeConnected Q) (ha : a ∈ Q) (hab : Adj a b) :
    EdgeConnected (insert b Q) := by
  have old : ∀ x ∈ Q, ∀ y ∈ Q,
      Relation.ReflTransGen (Step (insert b Q)) x y := by
    intro x hx y hy
    apply Relation.ReflTransGen.mono (fun _ _ h => ?_) x y (hQ.2 x hx y hy)
    exact ⟨Finset.mem_insert_of_mem h.1, Finset.mem_insert_of_mem h.2.1,h.2.2⟩
  have ab : Step (insert b Q) a b :=
    ⟨Finset.mem_insert_of_mem ha,Finset.mem_insert_self _ _,hab⟩
  have ba : Step (insert b Q) b a :=
    ⟨Finset.mem_insert_self _ _,Finset.mem_insert_of_mem ha,adj_symm hab⟩
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  intro x hx y hy
  rcases Finset.mem_insert.mp hx with rfl | hxOld
  · rcases Finset.mem_insert.mp hy with rfl | hyOld
    · exact .refl
    · exact (old a ha y hyOld).head ba
  · rcases Finset.mem_insert.mp hy with rfl | hyOld
    · exact (old x hxOld a ha).tail ab
    · exact old x hxOld y hyOld

theorem growth_sound {P : Finset GridPoint} (h : Grown P) : EdgeConnected P := by
  induction h with
  | singleton p => exact connected_singleton p
  | insert _ ha _ hab ih => exact connected_insert ih ha hab

theorem growth_iff_connected (P : Finset GridPoint) : Grown P ↔ EdgeConnected P :=
  ⟨growth_sound, growth_complete⟩

theorem translate_connected (t : GridPoint) {P : Finset GridPoint}
    (h : EdgeConnected P) : EdgeConnected (translate t P) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨p,hp⟩ := h.1
    exact ⟨_,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  · intro p hp q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    apply Relation.ReflTransGen.lift (fun p : GridPoint => (p.1+t.1,p.2+t.2))
      (fun x y hxy => ?_) a b (h.2 a ha b hb)
    exact ⟨Finset.mem_image.mpr ⟨x,hxy.1,rfl⟩,
      Finset.mem_image.mpr ⟨y,hxy.2.1,rfl⟩,(adj_translate t x y).mpr hxy.2.2⟩

-- Exact sound executable checker: every new cell attaches to the previous set.
def attachCheck (Q : Finset GridPoint) : List GridPoint → Bool
  | [] => true
  | b :: bs => (decide (∃ a ∈ Q, Adj a b)) && attachCheck (insert b Q) bs

theorem attachCheck_sound (Q : Finset GridPoint) (bs : List GridPoint)
    (hQ : EdgeConnected Q) (h : attachCheck Q bs = true) :
    EdgeConnected (Q ∪ bs.toFinset) := by
  induction bs generalizing Q with
  | nil => simpa using hQ
  | cons b bs ih =>
    simp only [attachCheck, Bool.and_eq_true] at h
    obtain ⟨a,ha,hab⟩ := of_decide_eq_true h.1
    have hc := ih (insert b Q) (connected_insert hQ ha hab) h.2
    simpa [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hc

-- Certificate placements are actual integer translations, with no range restriction.
def placementCheck (C : Finset GridPoint) (P : List GridPoint) (t : GridPoint) : Bool :=
  P.all (fun p => decide ((p.1+t.1,p.2+t.2) ∈ C))

theorem placementCheck_sound (C : Finset GridPoint) (P : List GridPoint) (t : GridPoint)
    (h : placementCheck C P t = true) : translate t P.toFinset ⊆ C := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  exact of_decide_eq_true (List.all_eq_true.mp h p (List.mem_toFinset.mp hp))

theorem minimumSize_le {n m : ℕ} (h : EligibleSize n m) : minimumSize n ≤ m := by
  classical
  rw [minimumSize, dite_eq_left (show ∃ k, EligibleSize n k from ⟨m,h⟩)]
  exact Nat.find_min' _ h

theorem refute_of_container (C : Finset GridPoint) (hcard : C.card = 57)
    (hC : UniversalContainer 11 C) : ¬ SourceFormula := by
  intro h
  have hle := minimumSize_le (n := 11) (m := 57) ⟨C,hcard,hC⟩
  have heq := h 11 (by decide)
  change minimumSize 11 = 58 at heq
  omega
end Polyomino57
