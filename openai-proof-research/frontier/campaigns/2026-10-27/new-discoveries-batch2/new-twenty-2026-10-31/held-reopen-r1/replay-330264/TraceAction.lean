import NormalForm
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RACGNormal330264
open RACGSemantics330264
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev ReducedList := {w : List V // Clean G w}
instance traceSetoid : Setoid (ReducedList G) where
  r w z := Shuffle G w.val z.val
  iseqv := ⟨fun w => .refl w.val, fun h => h.symm, fun h k => .trans h k⟩

abbrev Trace := Quotient (traceSetoid G)
def traceOf (w : List V) (hw : Clean G w) : Trace G := Quotient.mk _ ⟨w, hw⟩
def traceLength : Trace G → ℕ := Quotient.lift (fun w => w.val.length)
  (fun _ _ h => Shuffle.length G h)

def stepTrace (a : V) : Trace G → Trace G := Quotient.map
  (fun w : ReducedList G => ⟨toggle G a w.val, clean_toggle G a w.val w.property⟩)
  (fun _ _ h => toggle_shuffle G h a)

 theorem stepTrace_involutive (a : V) : Function.Involutive (stepTrace G a) := by
  intro q
  induction q using Quotient.inductionOn with
  | h w => exact Quotient.sound (toggle_involutive_shuffle G a w.val w.property)

def generatorPerm (a : V) : Equiv.Perm (Trace G) where
  toFun := stepTrace G a
  invFun := stepTrace G a
  left_inv := stepTrace_involutive G a
  right_inv := stepTrace_involutive G a

 theorem stepTrace_commute {a b : V} (hab : G.Adj a b) (q : Trace G) :
    stepTrace G a (stepTrace G b q) = stepTrace G b (stepTrace G a q) := by
  induction q using Quotient.inductionOn with
  | h w => exact Quotient.sound (toggle_commute_shuffle G hab w.val)

 theorem generatorPerm_sq (a : V) : generatorPerm G a * generatorPerm G a = 1 := by
  ext q
  exact stepTrace_involutive G a q

 theorem generatorPerm_commute {a b : V} (hab : G.Adj a b) :
    generatorPerm G a * generatorPerm G b = generatorPerm G b * generatorPerm G a := by
  ext q
  exact stepTrace_commute G hab q

 theorem action_liftable : (matrix G).IsLiftable (generatorPerm G) := by
  intro a b
  by_cases he : a = b
  · subst b
    simp only [matrix, ite_eq_left rfl, pow_one]
    exact generatorPerm_sq G a
  · by_cases hab : G.Adj a b
    · simp only [matrix, ite_eq_right he, ite_eq_left hab, pow_two]
      calc
        _ = generatorPerm G a * (generatorPerm G b * generatorPerm G a) * generatorPerm G b := by simp [mul_assoc]
        _ = generatorPerm G a * (generatorPerm G a * generatorPerm G b) * generatorPerm G b := by rw [generatorPerm_commute G hab]
        _ = 1 := by simp [← mul_assoc, generatorPerm_sq G]
    · simp [matrix, he, hab]

/-- A homomorphism out of the actual Mathlib PresentedGroup, constructed without a normal-form axiom. -/
def groupAction : RACG G →* Equiv.Perm (Trace G) :=
  (system G).lift ⟨generatorPerm G, action_liftable G⟩

@[simp] theorem groupAction_simple (a : V) :
    groupAction G ((system G).simple a) = generatorPerm G a :=
  (system G).lift_apply_simple (action_liftable G) a

 theorem traceLength_step (a : V) (q : Trace G) :
    traceLength G (stepTrace G a q) ≤ traceLength G q + 1 := by
  induction q using Quotient.inductionOn with
  | h w =>
    change (toggle G a w.val).length ≤ w.val.length + 1
    rcases toggle_length G a w.val with h | h <;> omega

 theorem action_word_length (w : List V) (q : Trace G) :
    traceLength G (groupAction G ((system G).wordProd w) q) ≤ traceLength G q + w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [CoxeterSystem.wordProd_cons, map_mul, groupAction_simple,
      Equiv.Perm.mul_apply]
    have h := traceLength_step G a (groupAction G ((system G).wordProd w) q)
    change traceLength G (stepTrace G a (groupAction G ((system G).wordProd w) q)) ≤ _
    simp only [List.length_cons]
    omega

 theorem action_clean_word (w : List V) (hw : Clean G w) :
    groupAction G ((system G).wordProd w) (traceOf G [] (clean_nil G)) = traceOf G w hw := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [CoxeterSystem.wordProd_cons, map_mul, groupAction_simple, Equiv.Perm.mul_apply]
    rw [ih hw.1]
    change (Quotient.mk (traceSetoid G) (⟨toggle G a w, clean_toggle G a w hw.1⟩ : ReducedList G)) = Quotient.mk (traceSetoid G) (⟨a :: w, hw⟩ : ReducedList G)
    apply Quotient.sound
    change Shuffle G (toggle G a w) (a :: w)
    rw [toggle, ite_eq_right hw.2]
    exact .refl _

/-- The genuine converse normal form, for every graph and every finite word. -/
 theorem clean_implies_reduced (w : List V) (hw : Clean G w) : (system G).IsReduced w := by
  obtain ⟨z, hz, he⟩ := (system G).exists_isReduced ((system G).wordProd w)
  have hbound := action_word_length G z (traceOf G [] (clean_nil G))
  rw [← he, action_clean_word G w hw] at hbound
  change w.length ≤ 0 + z.length at hbound
  have hz' := hz.eq
  rw [← he] at hz'
  have hu := (system G).length_wordProd_le w
  unfold CoxeterSystem.IsReduced
  omega

 theorem reduced_iff_clean (w : List V) : (system G).IsReduced w ↔ Clean G w :=
  ⟨reduced_implies_clean G w, clean_implies_reduced G w⟩

#print axioms groupAction
#print axioms clean_implies_reduced
#print axioms reduced_iff_clean
end RACGNormal330264
