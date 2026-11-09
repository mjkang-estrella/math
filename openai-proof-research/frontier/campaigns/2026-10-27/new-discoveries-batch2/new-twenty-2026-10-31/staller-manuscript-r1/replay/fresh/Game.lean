import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
set_option autoImplicit false
namespace MathDB355140
abbrev Board (n : ℕ) := Finset (Fin n)
def owns {n : ℕ} (G : SimpleGraph (Fin n)) (s : Board n) : Prop :=
  ∃ v, ∀ w, w = v ∨ G.Adj v w → w ∈ s
instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Board n) : Decidable (owns G s) := by
  unfold owns
  infer_instance
-- a is exactly the unclaimed board; s is Staller's claimed set.
-- A strategy is a finite tree: one legal choice for Staller, every legal response for Dominator.
inductive Wins {n : ℕ} (G : SimpleGraph (Fin n)) : Board n → Board n → Bool → ℕ → Prop
| done (s a : Board n) (turn : Bool) (b : ℕ) : owns G s → Wins G s a turn b
| staller (s a : Board n) (b : ℕ) (v : Fin n) : v ∈ a →
    Wins G (insert v s) (a.erase v) false b → Wins G s a true (b+1)
| dominator (s a : Board n) (b : ℕ) : a.Nonempty →
    (∀ v ∈ a, Wins G s (a.erase v) true b) → Wins G s a false b

def check {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s a : Board n) (turn : Bool) (b : ℕ) : Bool :=
  if owns G s then true else
  if turn then
    match b with
    | 0 => false
    | b+1 => decide (∃ v : a, check G (insert v.val s) (a.erase v.val) false b = true)
  else decide (a.Nonempty ∧ ∀ v : a, check G s (a.erase v.val) true b = true)
termination_by a.card
 decreasing_by all_goals exact Finset.card_erase_lt_of_mem (by aesop)

 theorem check_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s a : Board n) (turn : Bool) (b : ℕ) : check G s a turn b = true ↔ Wins G s a turn b := by
  induction ha : a.card using Nat.strong_induction_on generalizing s a turn b with
  | h k ih =>
    rw [check.eq_def]
    by_cases hs : owns G s
    · rw [ite_eq_left hs]
      exact ⟨fun _ => Wins.done s a turn b hs, fun _ => rfl⟩
    · rw [ite_eq_right hs]
      cases turn with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
        constructor
        · rintro ⟨hne, h⟩
          apply Wins.dominator s a b hne
          intro v hv
          exact (ih _ (ha ▸ Finset.card_erase_lt_of_mem hv) s (a.erase v) true b rfl).mp (h ⟨v,hv⟩)
        · intro hw
          cases hw with
          | done _ _ _ _ h => exact False.elim (hs h)
          | dominator _ _ _ hne h =>
            exact ⟨hne, fun v => (ih _ (ha ▸ Finset.card_erase_lt_of_mem v.property) s (a.erase v.val) true b rfl).mpr (h v.val v.property)⟩
      | true =>
        simp only [↓reduceIte]
        cases b with
        | zero =>
          simp only [Bool.false_eq_true, false_iff]
          intro hw
          cases hw with
          | done _ _ _ _ h => exact hs h
        | succ b =>
          simp only [decide_eq_true_eq]
          constructor
          · rintro ⟨⟨v,hv⟩, h⟩
            exact Wins.staller s a b v hv ((ih _ (ha ▸ Finset.card_erase_lt_of_mem hv) (insert v s) (a.erase v) false b rfl).mp h)
          · intro hw
            cases hw with
            | done _ _ _ _ h => exact False.elim (hs h)
            | staller _ _ _ v hv h =>
              exact ⟨⟨v, hv⟩, (ih _ (ha ▸ Finset.card_erase_lt_of_mem hv) (insert v s) (a.erase v) false b rfl).mpr h⟩

def edges : Finset (Fin 7 × Fin 7) :=
  {(0,1),(0,5),(1,2),(1,6),(2,3),(3,4),(4,5),(5,6)}
def graph : SimpleGraph (Fin 7) where
  Adj v w := (v,w) ∈ edges ∨ (w,v) ∈ edges
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by decide⟩
instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ edges ∨ _ ∈ edges))
def degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) : ℕ :=
  (Finset.univ.filter (G.Adj v)).card
def MinDegree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (δ : ℕ) : Prop :=
  (∀ v, δ ≤ degree G v) ∧ ∃ v, degree G v = δ
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem minimum_degree : MinDegree graph 2 := by unfold MinDegree; decide
 theorem four_check : check graph ∅ Finset.univ true 4 = true := by decide +kernel
 theorem three_check : check graph ∅ Finset.univ true 3 = false := by decide +kernel
 theorem wins_four : Wins graph ∅ Finset.univ true 4 :=
  (check_iff graph ∅ Finset.univ true 4).mp four_check
 theorem not_wins_three : ¬ Wins graph ∅ Finset.univ true 3 := by
  intro h
  have := (check_iff graph ∅ Finset.univ true 3).mpr h
  rw [three_check] at this
  contradiction
theorem Wins.mono {n : ℕ} {G : SimpleGraph (Fin n)} {s a : Board n} {turn : Bool} {b : ℕ}
    (h : Wins G s a turn b) : ∀ c, b ≤ c → Wins G s a turn c := by
  induction h with
  | done s a turn b h => exact fun c _ => Wins.done s a turn c h
  | staller s a b v hv h ih =>
    intro c hc
    cases c with
    | zero => omega
    | succ c => exact Wins.staller s a c v hv (ih c (by omega))
  | dominator s a b hne h ih =>
    exact fun c hc => Wins.dominator s a c hne (fun v hv => ih v hv c hc)

noncomputable def winningNumber {n : ℕ} (G : SimpleGraph (Fin n)) (turn : Bool) : WithTop ℕ := by
  classical
  exact if h : ∃ b, Wins G ∅ Finset.univ turn b then (Nat.find h : WithTop ℕ) else ⊤
theorem winning_number_four : winningNumber graph true = (4 : WithTop ℕ) := by
  classical
  have hex : ∃ b, Wins graph ∅ Finset.univ true b := ⟨4, wins_four⟩
  have hmin : Nat.find hex = 4 := by
    apply (Nat.find_eq_iff hex).mpr
    constructor
    · exact wins_four
    · intro b hb h
      exact not_wins_three (h.mono 3 (by omega))
  unfold winningNumber
  rw [dite_eq_left hex, hmin]
  rfl

-- Dominator has won exactly when his vertices meet every closed neighborhood.
-- Disjoint occupation makes the two terminal conditions incompatible.
theorem terminal_incompatibility {n : ℕ} (G : SimpleGraph (Fin n)) (s d : Board n)
    (hdis : Disjoint s d)
    (hdom : ∀ v, ∃ w, (w = v ∨ G.Adj v w) ∧ w ∈ d) : ¬ owns G s := by
  rintro ⟨v,hv⟩
  obtain ⟨w,hw,hd⟩ := hdom v
  exact (Finset.disjoint_left.mp hdis) (hv w hw) hd

theorem Wins.not_after_dominator {n : ℕ} {G : SimpleGraph (Fin n)} {s a : Board n}
    {turn : Bool} {b : ℕ} (h : Wins G s a turn b) :
    ∀ d : Board n, Disjoint s d → Disjoint a d →
    (∀ v, ∃ w, (w = v ∨ G.Adj v w) ∧ w ∈ d) → False := by
  induction h with
  | done s a turn b h =>
    exact fun d hs _ hd => terminal_incompatibility G s d hs hd h
  | staller s a b v hv h ih =>
    intro d hs ha hd
    apply ih d _ (Finset.disjoint_of_subset_left (Finset.erase_subset v a) ha) hd
    apply Finset.disjoint_insert_left.mpr
    exact ⟨fun hmem => Finset.disjoint_left.mp ha hv hmem, hs⟩
  | dominator s a b hne h ih =>
    intro d hs ha hd
    obtain ⟨v,hv⟩ := hne
    exact ih v hv d hs (Finset.disjoint_of_subset_left (Finset.erase_subset v a) ha) hd

-- Finite winning number bounded by B iff Staller has a strategy taking at most B moves.
-- The two conjuncts are precisely Conjecture 7.2(i) and (ii).
def BudgetClaim : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n))
  [DecidableRel G.Adj] (δ : ℕ), MinDegree G δ →
  ((∃ b, Wins G ∅ Finset.univ true b) → Wins G ∅ Finset.univ true ((n+1)/2-δ+1)) ∧
  ((∃ b, Wins G ∅ Finset.univ false b) → Wins G ∅ Finset.univ false (n/2-δ+1))
 theorem budget_refutation : ¬ BudgetClaim := by
  intro h
  have hw := (h 7 graph 2 minimum_degree).1 ⟨4, wins_four⟩
  exact not_wins_three hw
def SourceClaim : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n))
  [DecidableRel G.Adj] (δ : ℕ), MinDegree G δ →
  ((∃ b, Wins G ∅ Finset.univ true b) → ∃ b, Wins G ∅ Finset.univ true b ∧ b+δ ≤ (n+1)/2+1) ∧
  ((∃ b, Wins G ∅ Finset.univ false b) → ∃ b, Wins G ∅ Finset.univ false b ∧ b+δ ≤ n/2+1)
theorem source_refutation : ¬ SourceClaim := by
  intro h
  obtain ⟨b,hb,hbound⟩ := (h 7 graph 2 minimum_degree).1 ⟨4,wins_four⟩
  exact not_wins_three (hb.mono 3 (by omega))
#print axioms source_refutation
#print axioms winning_number_four
end MathDB355140

open Lean in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n, ci) in env.constants.toList do
  if (env.getModuleIdxFor? n).isNone then
   count := count + 1
   let axs ← Lean.collectAxioms n
   logInfo m!"AUDIT {n} TYPE {ci.type} AXIOMS {axs}"
   if ci.isUnsafe then throwError "unsafe {n}"
   if ci matches .axiomInfo _ then throwError "axiom {n}"
   for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
     throwError "forbidden {ax}"
 logInfo m!"AUDIT_TOTAL {count}"
