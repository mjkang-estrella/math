module
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public section
set_option autoImplicit false
set_option warningAsError true
namespace FactorialProduct

def qValue (t : ℕ) : ℚ := (t.factorial : ℚ) / (t : ℚ) ^ t
noncomputable def f (x : ℝ) : ℝ := Real.Gamma (x + 1) / x ^ x
def aList : List ℕ := [3,5,6,7,8,14,16,20,36]
def bList : List ℕ := [4,10,12,15,18,21,32]
def A : Finset ℕ := aList.toFinset
def B : Finset ℕ := bList.toFinset

theorem list_conditions : aList.Nodup ∧ bList.Nodup ∧
    (∀ t ∈ aList, 1 < t) ∧ (∀ t ∈ bList, 1 < t) ∧
    aList.length = 9 ∧ bList.length = 7 := by
  norm_num [aList, bList, List.nodup_cons, List.mem_cons]

theorem set_conditions : A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
    (∀ t ∈ A, 1 < t) ∧ (∀ t ∈ B, 1 < t) ∧ A.card = 9 ∧ B.card = 7 := by
  decide

theorem rational_equality : (aList.map qValue).prod = (bList.map qValue).prod := by
  norm_num [aList, bList, qValue, Nat.factorial]

theorem gamma_dictionary (t : ℕ) : f (t : ℝ) = (qValue t : ℝ) := by
  simp only [f, qValue, Real.Gamma_nat_eq_factorial, Real.rpow_natCast,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_pow]

theorem product_dictionary (l : List ℕ) :
    (l.map (fun (t : ℕ) => f (t : ℝ))).prod = ((l.map qValue).prod : ℚ) := by
  induction l with
  | nil => simp
  | cons t l ih => simpa only [List.map_cons, List.prod_cons, Rat.cast_mul,
      gamma_dictionary] using congrArg (fun x : ℝ => (qValue t : ℝ) * x) ih

theorem literal_list_equality :
    (aList.map (fun (t : ℕ) => f (t : ℝ))).prod =
    (bList.map (fun (t : ℕ) => f (t : ℝ))).prod := by
  rw [product_dictionary, product_dictionary, rational_equality]

theorem literal_set_equality : (∏ t ∈ A, f (t : ℝ)) = ∏ t ∈ B, f (t : ℝ) := by
  simpa [A, B, aList, bList] using literal_list_equality

def SourceStatement : Prop := ∀ l m : List ℕ,
  l.Nodup → m.Nodup → (∀ t ∈ l, 1 < t) → (∀ t ∈ m, 1 < t) →
  (l.map (fun (t : ℕ) => f (t : ℝ))).prod = (m.map (fun (t : ℕ) => f (t : ℝ))).prod →
  l.length = m.length ∧ l.Perm m

theorem source_statement_negation : ¬ SourceStatement := by
  intro h
  have e := (h aList bList list_conditions.1 list_conditions.2.1
    list_conditions.2.2.1 list_conditions.2.2.2.1 literal_list_equality).1
  norm_num [aList, bList] at e

def FinsetStatement : Prop := ∀ S T : Finset ℕ,
  (∀ t ∈ S, 1 < t) → (∀ t ∈ T, 1 < t) →
  (∏ t ∈ S, f (t : ℝ)) = (∏ t ∈ T, f (t : ℝ)) → S.card = T.card ∧ S = T

theorem finset_statement_negation : ¬ FinsetStatement := by
  intro h
  have e := (h A B set_conditions.2.2.2.1 set_conditions.2.2.2.2.1
    literal_set_equality).1
  rw [set_conditions.2.2.2.2.2.1, set_conditions.2.2.2.2.2.2] at e
  norm_num at e

theorem disjoint_nonempty_counterexample : ∃ S T : Finset ℕ,
    S.Nonempty ∧ T.Nonempty ∧ Disjoint S T ∧
    (∀ t ∈ S, 1 < t) ∧ (∀ t ∈ T, 1 < t) ∧ S.card = 9 ∧ T.card = 7 ∧
    (∏ t ∈ S, f (t : ℝ)) = ∏ t ∈ T, f (t : ℝ) := by
  exact ⟨A, B, set_conditions.1, set_conditions.2.1, set_conditions.2.2.1,
    set_conditions.2.2.2.1, set_conditions.2.2.2.2.1,
    set_conditions.2.2.2.2.2.1, set_conditions.2.2.2.2.2.2, literal_set_equality⟩

def IntegerSourceStatement : Prop := ∀ l m : List ℤ,
  l.Nodup → m.Nodup → (∀ t ∈ l, 1 < t) → (∀ t ∈ m, 1 < t) →
  (l.map (fun (t : ℤ) => f (t : ℝ))).prod =
    (m.map (fun (t : ℤ) => f (t : ℝ))).prod →
  l.length = m.length ∧ l.Perm m

theorem integer_source_statement_negation : ¬ IntegerSourceStatement := by
  intro h
  have eqn : ((aList.map (fun (t : ℕ) => (t : ℤ))).map (fun (t : ℤ) => f (t : ℝ))).prod =
      ((bList.map (fun (t : ℕ) => (t : ℤ))).map (fun (t : ℤ) => f (t : ℝ))).prod := by
    simpa only [List.map_map, Function.comp_def, Int.cast_natCast] using literal_list_equality
  have e := (h (aList.map (fun (t : ℕ) => (t : ℤ))) (bList.map (fun (t : ℕ) => (t : ℤ)))
    (by norm_num [aList, List.nodup_cons]) (by norm_num [bList, List.nodup_cons])
    (by norm_num [aList]) (by norm_num [bList]) eqn).1
  norm_num [aList, bList] at e

def StrongDistinctStatement : Prop := ∀ S T : Finset ℕ,
  S.Nonempty → T.Nonempty → Disjoint S T →
  (∀ t ∈ S, 1 < t) → (∀ t ∈ T, 1 < t) →
  (∏ t ∈ S, f (t : ℝ)) = (∏ t ∈ T, f (t : ℝ)) → S.card = T.card ∧ S = T

theorem strong_distinct_statement_negation : ¬ StrongDistinctStatement := by
  intro h
  have e := (h A B set_conditions.1 set_conditions.2.1 set_conditions.2.2.1
    set_conditions.2.2.2.1 set_conditions.2.2.2.2.1 literal_set_equality).1
  rw [set_conditions.2.2.2.2.2.1, set_conditions.2.2.2.2.2.2] at e
  norm_num at e
end FactorialProduct
