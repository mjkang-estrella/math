import KiralyCounterexample
open Lean Elab Command

-- statement fidelity: print exact definitions and endpoint types
#print KiralyClutter.IsClutter
#print KiralyClutter.IsTransversal
#print KiralyClutter.blocker
#print KiralyClutter.coveringPolyhedron
#print KiralyClutter.IsIdeal
#print KiralyClutter.KiralyProperty
#print KiralyClutter.KiralyConjecture
#check @KiralyClutter.kiraly_conjecture_false
#check @KiralyClutter.counterexample
#print KiralyClutter.C11

-- reviewer-stated bridges, proved here against the candidate's definitions
-- (1) refuting the one-directional (Pap TR Conj 1.2) form: nonideal ∧ ¬property
example : ¬ (∀ (V : Type) [Fintype V] [DecidableEq V] (C : Finset (Finset V)),
    KiralyClutter.IsClutter C → ¬ KiralyClutter.IsIdeal C → KiralyClutter.KiralyProperty C) :=
  fun h => KiralyClutter.counterexample.2.2 (h (Fin 11) KiralyClutter.C11
    KiralyClutter.counterexample.1 KiralyClutter.counterexample.2.1)

-- (2) Pap single-h form implies the (p,q) form, so ¬(p,q) ⇒ ¬h (no disjointness needed)
def SingleH {V : Type} [DecidableEq V] (C : Finset (Finset V)) : Prop :=
  ∃ h : Finset V → V, (∀ X ∈ C, h X ∈ X) ∧ (∀ Y ∈ KiralyClutter.blocker C, h Y ∈ Y) ∧
    ∀ X ∈ C, ∀ Y ∈ KiralyClutter.blocker C, h X = h Y → 1 < (X ∩ Y).card

theorem singleH_imp {V : Type} [DecidableEq V] (C : Finset (Finset V)) :
    SingleH C → KiralyClutter.KiralyProperty C := by
  rintro ⟨h, h1, h2, h3⟩
  exact ⟨fun X => h X.1, fun Y => h Y.1, fun X => h1 X.1 X.2, fun Y => h2 Y.1 Y.2,
    fun X Y e => h3 X.1 X.2 Y.1 Y.2 e⟩

theorem no_singleH : ¬ SingleH KiralyClutter.C11 :=
  fun h => KiralyClutter.counterexample.2.2 (singleH_imp _ h)

-- (3) the polyhedron is genuinely nonempty/pointed-relevant: x* has non-integer coordinate
example : ¬ ∃ z : ℤ, KiralyClutter.xstar 0 = z := by
  rintro ⟨z, hz⟩
  have : (z : ℝ) = 1/3 := by rw [← hz]; rfl
  have h1 : (0:ℝ) < z := by rw [this]; norm_num
  have h2 : (z:ℝ) < 1 := by rw [this]; norm_num
  have : 0 < z := by exact_mod_cast h1
  have : z < 1 := by exact_mod_cast h2
  omega

#print axioms no_singleH

-- list every declaration of the candidate module with its axioms; flag any `axiom` declaration
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `KiralyCounterexample | throwError "module not found"
  let names := env.constants.toList.filterMap fun (n, ci) =>
    if env.getModuleIdxFor? n == some idx then some (n, ci) else none
  let mut nAx : Nat := 0
  let mut bad : Array Name := #[]
  for (n, ci) in names do
    if ci matches .axiomInfo _ then nAx := nAx + 1; bad := bad.push n
    if n.isInternal then continue
    let axs ← Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        bad := bad.push (n ++ a)
  logInfo m!"module decls: {names.length}; axiom decls: {nAx}; offending: {bad}"
