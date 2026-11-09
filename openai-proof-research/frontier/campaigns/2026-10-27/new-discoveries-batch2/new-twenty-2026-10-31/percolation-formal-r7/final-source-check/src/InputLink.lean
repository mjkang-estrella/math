import PG5CNF
import RUP
namespace Percolation
set_option autoImplicit false
deriving instance DecidableEq for SatVar

def decodeVar (n : Nat) : SatVar :=
  if n < 31 then .a ⟨n % 31, Nat.mod_lt _ (by decide)⟩
  else if n < 62 then .x ⟨(n-31) % 31, Nat.mod_lt _ (by decide)⟩
  else if n < 93 then .i ⟨(n-62) % 31, Nat.mod_lt _ (by decide)⟩
  else if n < 124 then .j ⟨(n-93) % 31, Nat.mod_lt _ (by decide)⟩
  else .b ⟨((n-124)/31) % 31, Nat.mod_lt _ (by decide)⟩
    ⟨(n-124)%31, Nat.mod_lt _ (by decide)⟩

def decodeClause (c : CNF.NClause) : CNF.Clause SatVar :=
  c.map (fun z => (decodeVar z.1, z.2))
theorem holds_decode (v : SatVar → Bool) (c : CNF.NClause)
    (h : CNF.Holds v (decodeClause c)) : CNF.Holds (v ∘ decodeVar) c := by
  obtain ⟨z, hz, hv⟩ := h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
  exact ⟨w, hw, hv⟩
theorem input_gate (g : Gate5) (hg : g ∈ gates5) (c : CNF.NClause)
    (hc : decodeClause c ∈ CNF.gate g.1 g.2)
    (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) :
    CNF.Holds (v ∘ decodeVar) c := by
  apply holds_decode
  apply h
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨g, hg, hc⟩)
end Percolation
namespace Percolation
set_option autoImplicit false
theorem activationA_mem (l : Points 5) : activationGate5 SatVar.a (.i l) l ∈ gates5 := by
  simp only [gates5, List.mem_append, List.mem_map, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨l, by simp [pts5], rfl⟩)))
theorem activationX_mem (l : Points 5) : activationGate5 SatVar.x (.j l) l ∈ gates5 := by
  simp only [gates5, List.mem_append, List.mem_map, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨l, by simp [pts5], rfl⟩)))
theorem spread_mem (p : Points 5) : spreadGate5 p ∈ gates5 := by
  simp only [gates5, List.mem_append, List.mem_map, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inr ⟨p, by simp [pts5], rfl⟩))
theorem final_mem (p : Points 5) : finalGate5 p ∈ gates5 := by
  simp only [gates5, List.mem_append, List.mem_map, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨p, by simp [pts5], rfl⟩)
theorem closed_mem (v l : Points 5) : closedGate5 v l ∈ gates5 := by
  simp only [gates5, List.mem_append, List.mem_map, List.mem_flatMap]
  exact Or.inr ⟨v, by simp [pts5], l, by simp [pts5], rfl⟩
theorem hints_cons (val : Nat → Bool) (c : CNF.NClause) (cs : List CNF.NClause)
    (hc : CNF.Holds val c) (hs : ∀ d ∈ cs, CNF.Holds val d) :
    ∀ d ∈ c :: cs, CNF.Holds val d := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hc
  · exact hs d hd
end Percolation
namespace Percolation
set_option autoImplicit false
theorem input_nonfull (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) :
    CNF.Holds v (pts5.map (fun p => (SatVar.x p, true))) := by
  apply h
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (by simp)))
theorem input_omit (p : Points 5) (v : SatVar → Bool)
    (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds v (omitClause5 p) := by
  apply h
  apply List.mem_append_right
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨p, by simp [pts5], rfl⟩
theorem input_contain (p q : Points 5) (hne : q ≠ p) (v : SatVar → Bool)
    (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds v (containClause5 p q) := by
  apply h
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨p, by simp [pts5], List.mem_map.mpr ⟨q, ?_, rfl⟩⟩
  simp [pts5, hne]
end Percolation
