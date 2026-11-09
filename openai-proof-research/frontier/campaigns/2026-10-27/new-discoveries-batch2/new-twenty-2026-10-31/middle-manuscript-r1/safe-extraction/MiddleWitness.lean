import MiddleSmall
namespace R139.MiddleOCD
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
theorem ocd_G8 : ocd G8 = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨S0, ⟨S0_dom, S0_conn.preconnected⟩, by decide⟩
  · exact le_csInf ⟨4, S0, ⟨S0_dom, S0_conn.preconnected⟩, by decide⟩
      (fun k ⟨S, hS, hk⟩ => hk ▸ ocd_G8_lower S hS)

theorem ocd'_G8 : ocd' G8 = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨S0, ⟨S0_dom, S0_conn⟩, by decide⟩
  · exact le_csInf ⟨4, S0, ⟨S0_dom, S0_conn⟩, by decide⟩
      (fun k ⟨S, hS, hk⟩ => hk ▸ ocd'_G8_lower S hS)

/-! #### γ̃c(M(G8)) = 4 -/

/-- Edge of G8 from a Bool-certified pair. -/
def ed (a b : Fin 8) (h : adjB a b = true) : G8.edgeSet := ⟨s(a, b), (G8.mem_edgeSet).2 h⟩

/-- Perfect matching F = {01, 23, 46, 57}. -/
def mate : Fin 8 → G8.edgeSet := fun v =>
  if v = 0 ∨ v = 1 then ed 0 1 (by decide)
  else if v = 2 ∨ v = 3 then ed 2 3 (by decide)
  else if v = 4 ∨ v = 6 then ed 4 6 (by decide)
  else ed 5 7 (by decide)

theorem mate_mem : ∀ v, v ∈ ((mate v : G8.edgeSet) : Sym2 (Fin 8)) := by
  decide  -- PERF: unfolds `ed`, Sym2 membership on Fin 8; fallback: `intro v; fin_cases v <;> simp [mate, ed]`

def D8 : Finset (Fin 8 ⊕ G8.edgeSet) :=
  {Sum.inr (ed 0 1 (by decide)), Sum.inr (ed 2 3 (by decide)), Sum.inr (ed 4 6 (by decide)), Sum.inr (ed 5 7 (by decide))}

theorem D8_mate : ∀ v, Sum.inr (mate v) ∈ D8 := by
  intro v; fin_cases v <;> simp [mate, D8]

theorem D8_card : D8.card = 4 := by
  -- the four edges are distinct elements of Sym2 (Fin 8)
  decide  -- PERF/fallback: `simp [D8, ed, Sym2.eq_iff]`

theorem D8_dom : IsDominating (middle G8) D8 :=
  dominating_middle_of_mate G8 mate mate_mem D8 D8_mate

/-- Depth of a vertex in the spanning tree of G8 - F rooted at 6
(tree edges 06 16 56 67 27 37 47). -/
def dv (v : Fin 8) : ℕ := if v = 6 then 0 else if v = 2 ∨ v = 3 ∨ v = 4 then 2 else 1

/-- Tree parent in G8 - F. -/
def tp (v : Fin 8) : Fin 8 := if v = 2 ∨ v = 3 ∨ v = 4 then 7 else 6

/-- Key used to pick the shallower endpoint of an edge (injective). -/
def key (v : Fin 8) : ℕ := 8 * dv v + v.val

theorem key_inj : ∀ a b : Fin 8, key a = key b → a = b := by decide

/-- The endpoint of smaller key (the one closer to the root 6). -/
def lowEnd (e : Sym2 (Fin 8)) : Fin 8 :=
  Sym2.lift ⟨fun a b => if key a ≤ key b then a else b, fun a b => by fin_cases a <;> fin_cases b <;> decide⟩ e

theorem lowEnd_mem (e : Sym2 (Fin 8)) : lowEnd e ∈ e := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [lowEnd, Sym2.lift_mk]
    split_ifs
    · exact Sym2.mem_mk_left a b
    · exact Sym2.mem_mk_right a b

/-- Parent map on M(G8) - D8 towards the root `inl 6`. -/
def parM : Fin 8 ⊕ G8.edgeSet → Fin 8 ⊕ G8.edgeSet
  | Sum.inl v => if h : adjB v (tp v) = true then Sum.inr (ed v (tp v) h) else Sum.inl v
  | Sum.inr e => Sum.inl (lowEnd (e : Sym2 (Fin 8)))

def depM : Fin 8 ⊕ G8.edgeSet → ℕ
  | Sum.inl v => 2 * dv v
  | Sum.inr e => 2 * dv (lowEnd (e : Sym2 (Fin 8))) + 1

/-- Tree edges 06 16 56 67 27 37 47 are edges of G8 and avoid the matching. -/
theorem tree_ok : ∀ w : Fin 8, w ≠ 6 →
    ∃ h : adjB w (tp w) = true, Sum.inr (ed w (tp w) h) ∉ D8 ∧
      2 * dv (lowEnd s(w, tp w)) + 1 < 2 * dv w := by
  -- PERF/fallback: `intro w hw; fin_cases w <;> simp_all <;> decide`
  decide

theorem M8_conn : ((middle G8).induce ((D8 : Set (Fin 8 ⊕ G8.edgeSet))ᶜ)).Connected := by
  apply connected_of_parent (middle G8) _ (Sum.inl 6) (by simp [D8]) parM depM
  rintro (w | e) hT hne
  · have hw : w ≠ 6 := fun h => hne (by rw [h])
    obtain ⟨h, hnot, hlt⟩ := tree_ok w hw
    have hp : parM (Sum.inl w) = Sum.inr (ed w (tp w) h) := by simp [parM, h]
    rw [hp]
    refine ⟨by simpa using hnot, ?_, ?_⟩
    · -- adjacency vertex–edge is incidence
      show w ∈ s(w, tp w)
      exact Sym2.mem_mk_left _ _
    · simpa [depM, ed] using hlt
  · refine ⟨?_, ?_, ?_⟩
    · simp [parM, D8]
    · show lowEnd (e : Sym2 (Fin 8)) ∈ (e : Sym2 (Fin 8))
      exact lowEnd_mem _
    · simp [parM, depM]

theorem G8_par : ∀ v : Fin 8, v ≠ 6 → G8.Adj v (tp v) ∧ dv (tp v) < dv v := by decide

theorem G8_connected : G8.Connected := by
  have h := connected_of_parent G8 Set.univ 6 (Set.mem_univ _) tp dv
    (fun v _ hv => ⟨Set.mem_univ _, (G8_par v hv).1, (G8_par v hv).2⟩)
  exact (SimpleGraph.induceUnivIso G8).connected_iff.mp h

theorem ocd_M8_lower (S : Finset (Fin 8 ⊕ G8.edgeSet)) (h : IsDominating (middle G8) S) :
    4 ≤ S.card := by
  have := two_mul_card_ge_of_dominating_middle G8 S h
  simp only [Fintype.card_fin] at this
  omega

theorem ocd_M8 : ocd (middle G8) = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨D8, ⟨D8_dom, M8_conn.preconnected⟩, D8_card⟩
  · exact le_csInf ⟨4, D8, ⟨D8_dom, M8_conn.preconnected⟩, D8_card⟩
      (fun k ⟨S, hS, hk⟩ => hk ▸ ocd_M8_lower S hS.1)

theorem ocd'_M8 : ocd' (middle G8) = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨D8, ⟨D8_dom, M8_conn⟩, D8_card⟩
  · exact le_csInf ⟨4, D8, ⟨D8_dom, M8_conn⟩, D8_card⟩
      (fun k ⟨S, hS, hk⟩ => hk ▸ ocd_M8_lower S hS.1)


end R139.MiddleOCD
