import AutomatonSemantics
noncomputable section
set_option linter.unusedSectionVars false
namespace RACGNormal330264.Machine
open RACGSemantics330264
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {S : Type*} (M : Machine G S)

noncomputable def run : S → List V → Option S
  | s, [] => some s
  | s, a :: w => (M.next s a).bind (fun t => run t w)

 theorem run_context (s t : S) (u w : List V) (hu : Clean G u)
    (hs : M.state s = frontState G u) (hr : M.run s w = some t) :
    Clean G (w.reverse ++ u) ∧ M.state t = frontState G (w.reverse ++ u) := by
  induction w generalizing s u with
  | nil =>
    have he : s = t := Option.some.inj hr
    subst t
    simpa using And.intro hu hs
  | cons a w ih =>
    have ha : a ∈ M.state s ↔ Movable G a u := by rw [hs, mem_frontState]
    have hm : ¬ Movable G a u := by
      intro hm
      have hn := (M.next_spec s a).1 (ha.mpr hm)
      simp [run, hn] at hr
    obtain ⟨r, hn, hst⟩ := (M.next_spec s a).2 (fun h => hm (ha.mp h))
    have hr' : M.run r w = some t := by simpa [run, hn] using hr
    have hs' : M.state r = frontState G (a :: u) := by rw [hst, hs]; rfl
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append]
      using ih r (a :: u) ⟨hu, hm⟩ hs' hr'

/-- Every successful clique state is exactly the movable suffix set of the input word. -/
 theorem run_state_exact (w : List V) (s : S) (h : M.run M.initial w = some s) :
    M.state s = suffixState G w ∧ (system G).IsReduced w := by
  obtain ⟨hc, hs⟩ := M.run_context M.initial s [] w (clean_nil G)
    (by simpa [frontState] using M.initial_empty) h
  simp only [List.append_nil] at hc hs
  exact ⟨hs, (CoxeterSystem.isReduced_reverse_iff (system G) w).mp
    (clean_implies_reduced G w.reverse hc)⟩

 theorem run_accept (s : S) (w : List V) : M.Accept s w ↔ ∃ t, M.run s w = some t := by
  induction w generalizing s with
  | nil => simp [Accept, run]
  | cons a w ih =>
    cases hn : M.next s a with
    | none => simp [Accept, run, hn]
    | some r => simp [Accept, run, hn, ih]

 theorem failure_iff_not_reduced (w : List V) : M.run M.initial w = none ↔ ¬ (system G).IsReduced w := by
  rw [← M.accepts_iff_reduced w, M.run_accept]
  cases M.run M.initial w <;> simp

#print axioms run_state_exact
#print axioms failure_iff_not_reduced
end RACGNormal330264.Machine
