# Lean source appendix for MathDB 331692

Modules are in import order.

### `HexagonTransfer.lean`

```lean
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FinCases

namespace Helicene

inductive Turn where
  | left | straight | right
  deriving DecidableEq, Repr

def Turn.all : List Turn := [.left, .straight, .right]

theorem Turn.mem_all (t : Turn) : t ∈ Turn.all := by
  cases t <;> decide

def Turn.reflect : Turn → Turn
  | .left => .right
  | .straight => .straight
  | .right => .left

def Turn.offset : Turn → Fin 6
  | .left => 2
  | .straight => 3
  | .right => 4

abbrev Status := Fin 3
abbrev State := Fin 9
abbrev Vertex := Fin 6
abbrev Choice := Vertex → Bool

def frontStatus (s : State) (i : Vertex) : Status :=
  if i = 0 then ⟨s.val / 3, by omega⟩ else
  if i = 1 then ⟨s.val % 3, by omega⟩ else 0

def state (a b : Status) : State := ⟨3 * a.val + b.val, by omega⟩

def port (outgoing : Option Turn) (i : Vertex) : Bool :=
  match outgoing with
  | none => false
  | some t => i == t.offset || i == t.offset + 1

/-- The bit at vertex i selects edge {i,i+1}. -/
def touched (choice : Choice) (i : Vertex) : Bool := choice i || choice (i-1)

def prior (incoming : Option State) (i : Vertex) : Status :=
  (incoming.map (fun s => frontStatus s i)).getD 0

def matched (incoming : Option State) (choice : Choice) (i : Vertex) : Bool :=
  touched choice i || prior incoming i == 1

def required (incoming : Option State) (outgoing : Option Turn)
    (choice : Choice) (i : Vertex) : Bool :=
  !matched incoming choice i &&
    (prior incoming i == 2 ||
      (!port outgoing (i-1) && !matched incoming choice (i-1)) ||
      (!port outgoing (i+1) && !matched incoming choice (i+1)))

def localValid (incoming : Option State) (outgoing : Option Turn) (choice : Choice) : Prop :=
  (incoming.isSome → choice 0 = false) ∧
  (∀ i : Vertex, ¬ (choice i = true ∧ choice (i-1) = true)) ∧
  (∀ i : Vertex, touched choice i = true → prior incoming i ≠ 1) ∧
  (∀ i : Vertex, required incoming outgoing choice i = true → port outgoing i = true)

instance (a : Option State) (b : Option Turn) (c : Choice) : Decidable (localValid a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def outputState (incoming : Option State) (t : Turn) (choice : Choice) : State :=
  let status := fun i =>
    if matched incoming choice i then (1 : Status)
    else if required incoming (some t) choice i then 2 else 0
  state (status (t.offset + 1)) (status t.offset)

def choices : List Choice :=
  (List.range 64).map fun b i => b.testBit i.val

def transferCount (a : Option State) (b : Option Turn) (output : State) : ℤ :=
  (choices.countP fun c =>
    decide (localValid a b c) &&
      match b with
      | none => true
      | some t => outputState a t c == output : ℕ)

abbrev Square := Matrix State State ℤ
abbrev Row := State → ℤ

def start : Row := ![1,1,0,1,3,1,0,1,1]
def finish : Row := ![3,3,2,3,2,2,2,2,1]
def mat : Turn → Square
  | .left => !![0,1,0,0,2,1,0,1,1;
    1,0,0,1,2,0,1,0,0;
    0,1,0,0,1,0,0,1,0;
    0,1,1,0,2,1,0,0,0;
    1,0,0,1,1,0,0,0,0;
    0,1,0,0,1,0,0,0,0;
    0,0,0,0,2,1,0,1,1;
    0,0,0,1,1,0,1,0,0;
    0,0,0,0,1,0,0,1,0]
  | .straight => !![1,1,0,1,1,0,0,0,0;
    0,1,1,0,2,1,0,0,0;
    1,0,0,1,1,0,0,0,0;
    0,0,0,1,2,0,1,1,0;
    0,0,0,0,2,1,0,1,1;
    0,0,0,1,1,0,1,0,0;
    1,1,0,0,1,0,0,0,0;
    0,1,1,0,1,0,0,0,0;
    1,0,0,0,1,0,0,0,0]
  | .right => !![0,0,0,1,2,1,0,1,1;
    0,0,0,1,2,0,1,1,0;
    0,0,0,0,2,1,0,1,1;
    1,1,1,0,2,0,0,0,0;
    1,1,0,0,1,0,0,0,0;
    0,1,1,0,1,0,0,0,0;
    0,0,0,1,1,1,0,0,0;
    0,0,0,1,1,0,0,0,0;
    0,0,0,0,1,1,0,0,0]

def swap : Square := Matrix.of fun i j =>
  if j = state (frontStatus i 1) (frontStatus i 0) then 1 else 0

def L : Square := mat .left
def S : Square := mat .straight
def R : Square := mat .right

theorem start_nonneg (i : State) : 0 ≤ start i := by
  fin_cases i <;> decide

theorem finish_nonneg (i : State) : 0 ≤ finish i := by
  fin_cases i <;> decide

theorem mat_nonneg (t : Turn) (i j : State) : 0 ≤ mat t i j := by
  cases t <;> fin_cases i <;> fin_cases j <;> decide

set_option maxHeartbeats 5000000 in
theorem transfer_tables :
    (∀ j, start j = transferCount none (some .left) j) ∧
    (∀ i, finish i = transferCount (some i) none 0) ∧
    (∀ i j, L i j = transferCount (some i) (some .left) j) ∧
    (∀ i j, S i j = transferCount (some i) (some .straight) j) ∧
    (∀ i j, R i j = transferCount (some i) (some .right) j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (intro i j; fin_cases i <;> fin_cases j <;> decide) | (intro i; fin_cases i <;> decide)

theorem single_transfer : transferCount none none 0 = 5 := by decide

end Helicene
```

### `HexagonCertificate.lean`

```lean
import HexagonTransfer
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int

open Matrix

namespace Helicene

def word : List Turn → Square
  | [] => 1
  | t :: p => mat t * word p

@[simp] theorem word_append (p q : List Turn) : word (p ++ q) = word p * word q := by
  induction p with
  | nil => simp [word]
  | cons t p ih => simp [word, ih, mul_assoc]

@[simp] theorem word_single (t : Turn) : word [t] = mat t := by simp [word]

@[simp] theorem word_replicate (t : Turn) (h : ℕ) :
    word (List.replicate h t) = mat t ^ h := by
  induction h with
  | zero => rfl
  | succ h ih => rw [List.replicate_succ, word, ih, pow_succ']

def score (p : List Turn) : ℤ := start ⬝ᵥ (word p *ᵥ finish)

def Good (x : Row) : Prop := ∀ p : List Turn, 0 ≤ start ⬝ᵥ (word p *ᵥ x)

theorem mulVec_nonneg' {A : Square} {x : Row} (hA : ∀ i j, 0 ≤ A i j)
    (hx : ∀ i, 0 ≤ x i) (i : State) : 0 ≤ (A *ᵥ x) i :=
  dotProduct_nonneg_of_nonneg (Pi.le_def.mpr (hA i)) (Pi.le_def.mpr hx)

theorem good_of_nonneg {x : Row} (hx : ∀ i, 0 ≤ x i) : Good x := by
  intro p
  apply dotProduct_nonneg_of_nonneg (Pi.le_def.mpr start_nonneg)
  change ∀ i, (0 : ℤ) ≤ (word p *ᵥ x) i
  induction p with
  | nil => simpa [word] using hx
  | cons t p ih =>
    simpa only [word, mulVec_mulVec] using
      mulVec_nonneg' (mat_nonneg t) ih

theorem good_step {x : Row} (h : 0 ≤ start ⬝ᵥ x) (hs : ∀ t, Good (mat t *ᵥ x)) :
    Good x := by
  intro p
  induction p using List.reverseRecOn with
  | nil => simpa [word] using h
  | append_singleton p t _ =>
    simpa only [word_append, word_single, mulVec_mulVec] using hs t p

theorem good_mulVec {A : Square} (hA : ∀ j, Good (fun i => A i j))
    {x : Row} (hx : ∀ j, 0 ≤ x j) : Good (A *ᵥ x) := by
  intro p
  rw [dotProduct_mulVec, dotProduct_mulVec]
  apply dotProduct_nonneg_of_nonneg _ (Pi.le_def.mpr hx)
  change ∀ j, (0 : ℤ) ≤ _
  intro j
  simpa only [vecMul, dotProduct_mulVec] using hA j p

theorem left_power_nonneg (h : ℕ) : ∀ i, 0 ≤ (L ^ h *ᵥ finish) i := by
  simpa only [word_replicate, L] using
    (show ∀ i, 0 ≤ (word (List.replicate h Turn.left) *ᵥ finish) i from by
      generalize List.replicate h Turn.left = p
      induction p with
      | nil => simpa [word] using finish_nonneg
      | cons t p ih => simpa only [word, mulVec_mulVec] using mulVec_nonneg' (mat_nonneg t) ih)

def cert (depth : ℕ) (x : Vector ℤ 9) : Bool :=
  match depth with
  | 0 => (List.finRange 9).all (fun i => decide (0 ≤ x.get i))
  | d + 1 => decide (0 ≤ start ⬝ᵥ x.get) &&
      Turn.all.all (fun t => cert d (Vector.ofFn (mat t *ᵥ x.get)))

theorem cert_sound (depth : ℕ) (x : Vector ℤ 9) (h : cert depth x = true) :
    Good x.get := by
  induction depth generalizing x with
  | zero =>
    apply good_of_nonneg
    intro i
    exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))
  | succ d ih =>
    simp only [cert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    apply good_step h.1
    intro t
    have hg : (Vector.ofFn (mat t *ᵥ x.get)).get = mat t *ᵥ x.get := by
      funext i
      simp [Vector.get]
      exact congrArg _ (Fin.ext rfl)
    rw [← hg]
    exact ih _ (h.2 t (Turn.mem_all t))

def deltaSwitch : Square := L * (swap - 1)
def deltaStraight : Square := S - R * swap
def deltaLLR : Square := L * L * R - L * L * L
def deltaLRL : Square := L * R * L - L * L * L
def deltaSLR : Square := S * L * R - L * L * L

end Helicene
```

### `HexagonCutoff.lean`

```lean
import HexagonCertificate

open Matrix

namespace Helicene

def applyPower (h : ℕ) (x : Vector ℤ 9) : Vector ℤ 9 :=
  match h with
  | 0 => x
  | m + 1 => Vector.ofFn (L *ᵥ (applyPower m x).get)

theorem get_ofFn (y : Row) : (Vector.ofFn y).get = y := by
  funext i
  simp [Vector.get]
  exact congrArg _ (Fin.ext rfl)

theorem applyPower_eq (h : ℕ) (x : Vector ℤ 9) :
    (applyPower h x).get = L ^ h *ᵥ x.get := by
  induction h with
  | zero => simp [applyPower]
  | succ h ih =>
    rw [applyPower, get_ofFn, ih, pow_succ', ← mulVec_mulVec]

def powerCert (D : Square) (h : ℕ) (x : Row) : Bool :=
  cert 4 (Vector.ofFn (D *ᵥ (applyPower h (Vector.ofFn x)).get))

theorem powerCert_sound {D : Square} {h : ℕ} {x : Row}
    (hc : powerCert D h x = true) : Good (D *ᵥ (L ^ h *ᵥ x)) := by
  simpa only [get_ofFn, applyPower_eq] using cert_sound _ _ hc

def unit (j : State) : Row := Pi.single j 1

theorem cutoff {D : Square} {b : ℕ}
    (hc : ∀ i : Fin 7, b ≤ i.val → powerCert D i.val finish = true)
    (h7 : ∀ j, powerCert D 7 (unit j) = true) {m : ℕ} (hm : b ≤ m) :
    Good (D *ᵥ (L ^ m *ᵥ finish)) := by
  by_cases hsmall : m < 7
  · exact powerCert_sound (hc ⟨m,hsmall⟩ hm)
  · have hsplit : m = 7 + (m-7) := by omega
    have hp : L ^ m = L ^ 7 * L ^ (m-7) := by
      conv_lhs => rw [hsplit, pow_add]
    rw [hp]
    rw [mulVec_mulVec, ← mul_assoc, ← mulVec_mulVec]
    apply good_mulVec _ (left_power_nonneg (m-7))
    intro j
    have he : (D * L ^ 7) *ᵥ unit j = fun i => (D * L ^ 7) i j := by
      exact mulVec_single_one (D * L ^ 7) j
    rw [← he, ← mulVec_mulVec]
    exact powerCert_sound (h7 j)

set_option maxHeartbeats 0 in
theorem switch_good {h : ℕ} (hh : 2 ≤ h) : Good (deltaSwitch *ᵥ (L ^ h *ᵥ finish)) := by
  apply cutoff (b := 2) _ _ hh
  · intro i hi
    fin_cases i <;> first | (exfalso; exact (by decide : ¬ 2 ≤ _) hi) | decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxHeartbeats 0 in
theorem straight_good (h : ℕ) : Good (deltaStraight *ᵥ (L ^ h *ᵥ finish)) := by
  apply cutoff (b := 0) _ _ (Nat.zero_le h)
  · intro i _
    fin_cases i <;> decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

set_option maxHeartbeats 0 in
theorem llr_good : Good (deltaLLR *ᵥ finish) := by
  rw [← get_ofFn (deltaLLR *ᵥ finish)]
  exact cert_sound 3 _ (by decide +kernel)

set_option maxHeartbeats 0 in
theorem lrl_good : Good (deltaLRL *ᵥ finish) := by
  rw [← get_ofFn (deltaLRL *ᵥ finish)]
  exact cert_sound 3 _ (by decide +kernel)

set_option maxHeartbeats 0 in
theorem slr_good : Good (deltaSLR *ᵥ finish) := by
  rw [← get_ofFn (deltaSLR *ᵥ finish)]
  exact cert_sound 3 _ (by decide +kernel)

#print axioms switch_good
#print axioms straight_good
#print axioms llr_good
#print axioms lrl_good
#print axioms slr_good

end Helicene
```

### `HexagonMinimum.lean`

```lean
import HexagonCutoff

open Matrix

namespace Helicene

set_option maxHeartbeats 1000000

theorem reflection_comm (t : Turn) : mat t.reflect * swap = swap * mat t := by
  ext i j
  cases t <;> fin_cases i <;> fin_cases j <;> decide +kernel

theorem swap_finish : swap *ᵥ finish = finish := by
  funext i
  fin_cases i <;> decide +kernel

theorem start_swap : start ᵥ* swap = start := by
  funext i
  fin_cases i <;> decide +kernel

theorem reflect_apply (p : List Turn) :
    word (p.map Turn.reflect) *ᵥ finish = swap *ᵥ (word p *ᵥ finish) := by
  induction p with
  | nil => simp [word, swap_finish]
  | cons t p ih =>
    simp only [List.map_cons, word]
    rw [← mulVec_mulVec, ih]
    simp only [mulVec_mulVec]
    rw [← mul_assoc (mat t.reflect), reflection_comm, mul_assoc]

theorem score_reflect (p : List Turn) : score (p.map Turn.reflect) = score p := by
  rw [score, reflect_apply, dotProduct_mulVec, start_swap, score]

theorem power_reflect (h : ℕ) :
    R ^ h *ᵥ finish = swap *ᵥ (L ^ h *ᵥ finish) := by
  simpa [List.map_replicate, L, R, Turn.reflect] using reflect_apply (List.replicate h .left)

def continued (p : List Turn) (x : Row) : ℤ := start ⬝ᵥ (word p *ᵥ x)

theorem continued_sub (p : List Turn) (x y : Row) :
    continued p (x-y) = continued p x - continued p y := by
  simp [continued, mulVec_sub, dotProduct_sub]

theorem score_append (p q : List Turn) :
    score (p ++ q) = continued p (word q *ᵥ finish) := by
  simp only [score, word_append, ← mulVec_mulVec, continued]

theorem switch_replace (p : List Turn) (h : ℕ) (hh : 2 ≤ h) :
    score (p ++ List.replicate (h+1) .left) ≤
      score (p ++ .left :: List.replicate h .right) := by
  have hg := switch_good hh p
  change 0 ≤ continued p (deltaSwitch *ᵥ (L ^ h *ᵥ finish)) at hg
  rw [deltaSwitch, ← mulVec_mulVec, sub_mulVec, one_mulVec, mulVec_sub,
    continued_sub] at hg
  rw [score_append, score_append, word_replicate, pow_succ', word, word_replicate,
    ← mulVec_mulVec, ← mulVec_mulVec]
  change continued p (L *ᵥ (L ^ h *ᵥ finish)) ≤
    continued p (L *ᵥ (R ^ h *ᵥ finish))
  rw [power_reflect]
  exact sub_nonneg.mp hg

theorem straight_replace (p : List Turn) (h : ℕ) :
    score (p ++ List.replicate (h+1) .right) ≤
      score (p ++ .straight :: List.replicate h .left) := by
  have hg := straight_good h p
  change 0 ≤ continued p (deltaStraight *ᵥ (L ^ h *ᵥ finish)) at hg
  rw [deltaStraight, sub_mulVec, ← mulVec_mulVec, continued_sub] at hg
  rw [score_append, score_append, word_replicate, pow_succ', word, word_replicate,
    ← mulVec_mulVec, ← mulVec_mulVec]
  change continued p (R *ᵥ (R ^ h *ᵥ finish)) ≤
    continued p (S *ᵥ (L ^ h *ᵥ finish))
  rw [power_reflect]
  exact sub_nonneg.mp hg

theorem score_le_of_good (p a b : List Turn) (h : Good ((word a - word b) *ᵥ finish)) :
    score (p ++ b) ≤ score (p ++ a) := by
  have hg := h p
  change 0 ≤ continued p ((word a - word b) *ᵥ finish) at hg
  rw [sub_mulVec, continued_sub, ← score_append, ← score_append] at hg
  exact sub_nonneg.mp hg

theorem llr_replace (p : List Turn) :
    score (p ++ [.left,.left,.left]) ≤ score (p ++ [.left,.left,.right]) := by
  apply score_le_of_good p [.left,.left,.right] [.left,.left,.left]
  simpa only [word, mul_one, L, R, deltaLLR, mul_assoc] using llr_good

theorem lrl_replace (p : List Turn) :
    score (p ++ [.left,.left,.left]) ≤ score (p ++ [.left,.right,.left]) := by
  apply score_le_of_good p [.left,.right,.left] [.left,.left,.left]
  simpa only [word, mul_one, L, R, deltaLRL, mul_assoc] using lrl_good

theorem slr_replace (p : List Turn) :
    score (p ++ [.left,.left,.left]) ≤ score (p ++ [.straight,.left,.right]) := by
  apply score_le_of_good p [.straight,.left,.right] [.left,.left,.left]
  simpa only [word, mul_one, L, R, S, deltaSLR, mul_assoc] using slr_good

theorem lr_eq_ll : score [.left,.right] = score [.left,.left] := by decide +kernel

theorem replicate_reflect (h : ℕ) :
    score (List.replicate h .right) = score (List.replicate h .left) := by
  simpa [List.map_replicate, Turn.reflect] using score_reflect (List.replicate h .left)

theorem switch_replace_reflected (p : List Turn) (h : ℕ) (hh : 2 ≤ h) :
    score (p ++ List.replicate (h+1) .right) ≤
      score (p ++ .right :: List.replicate h .left) := by
  have hu := score_reflect (p ++ List.replicate (h+1) .right)
  have hv := score_reflect (p ++ .right :: List.replicate h .left)
  rw [← hu, ← hv]
  simpa [List.map_append, List.map_replicate, Turn.reflect] using
    switch_replace (p.map Turn.reflect) h hh

-- The two reflected last triples for a run ending in R,L.
theorem rrl_replace (p : List Turn) :
    score (p ++ [.right,.right,.right]) ≤ score (p ++ [.right,.right,.left]) := by
  rw [← score_reflect (p ++ _), ← score_reflect (p ++ _)]
  simpa [List.map_append, Turn.reflect] using llr_replace (p.map Turn.reflect)

theorem srl_replace (p : List Turn) :
    score (p ++ [.right,.right,.right]) ≤ score (p ++ [.straight,.right,.left]) := by
  rw [← score_reflect (p ++ _), ← score_reflect (p ++ _)]
  simpa [List.map_append, Turn.reflect] using slr_replace (p.map Turn.reflect)

def RunBound (p : List Turn) (t : Turn) (h : ℕ) : Prop :=
  score (List.replicate (p.length+h) .left) ≤ score (p ++ List.replicate h t)

theorem bound_with_run (p : List Turn) (t : Turn) (h : ℕ)
    (ht : t ≠ .straight) (hh : 0 < h) : RunBound p t h := by
  have aux (k : ℕ) : ∀ (p : List Turn) (t : Turn) (h : ℕ),
      p.length = k → t ≠ .straight → 0 < h → RunBound p t h := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have leftBound (p : List Turn) (h : ℕ) (hk : p.length = k) (hh : 0 < h) :
          RunBound p .left h := by
        cases p using List.reverseRecOn with
        | nil => simp [RunBound]
        | append_singleton q a =>
          have hq : q.length < k := by simp at hk; omega
          cases a with
          | left =>
            have hb := ih q.length hq q .left (h+1) rfl (by decide) (by omega)
            unfold RunBound at hb ⊢
            have hl : (q ++ [Turn.left]).length + h = q.length+(h+1) := by simp; omega
            rw [hl]
            simpa only [List.replicate_succ, List.append_assoc, List.singleton_append] using hb
          | straight =>
            have hb := ih q.length hq q .right (h+1) rfl (by decide) (by omega)
            have hc := hb.trans (straight_replace q h)
            simpa [RunBound, List.append_assoc, Nat.add_right_comm, Nat.add_assoc] using hc
          | right =>
            by_cases hlong : 2 ≤ h
            · have hb := ih q.length hq q .right (h+1) rfl (by decide) (by omega)
              have hc := hb.trans (switch_replace_reflected q h hlong)
              simpa [RunBound, List.append_assoc, Nat.add_right_comm, Nat.add_assoc] using hc
            · have he : h = 1 := by omega
              subst h
              cases q using List.reverseRecOn with
              | nil =>
                change score [.left,.left] ≤ score [.right,.left]
                have hr := score_reflect [.right,.left]
                change score [.left,.right] = score [.right,.left] at hr
                rw [← hr, lr_eq_ll]
              | append_singleton u b =>
                have hu : u.length < k := by simp at hk; omega
                cases b with
                | left =>
                  have hb := ih u.length hu u .left 3 rfl (by decide) (by omega)
                  simpa [RunBound, List.append_assoc, Nat.add_assoc] using
                    hb.trans (lrl_replace u)
                | straight =>
                  have hb := ih u.length hu u .right 3 rfl (by decide) (by omega)
                  simpa [RunBound, List.append_assoc, Nat.add_assoc] using
                    hb.trans (srl_replace u)
                | right =>
                  have hb := ih u.length hu u .right 3 rfl (by decide) (by omega)
                  simpa [RunBound, List.append_assoc, Nat.add_assoc] using
                    hb.trans (rrl_replace u)
      intro p t h hk ht hh
      cases t with
      | left => exact leftBound p h hk hh
      | straight => exact (ht rfl).elim
      | right =>
        have hb := leftBound (p.map Turn.reflect) h (by simpa using hk) hh
        have hr := score_reflect (p ++ List.replicate h .right)
        rw [List.map_append, List.map_replicate] at hr
        simpa [RunBound, ← hr, Turn.reflect] using hb
  exact aux p.length p t h rfl ht hh

theorem transfer_minimum (p : List Turn) :
    score (List.replicate p.length .left) ≤ score p := by
  cases p using List.reverseRecOn with
  | nil => simp
  | append_singleton q t =>
    cases t with
    | left => simpa [RunBound] using bound_with_run q .left 1 (by decide) (by decide)
    | right => simpa [RunBound] using bound_with_run q .right 1 (by decide) (by decide)
    | straight =>
      have hb := bound_with_run q .right 1 (by decide) (by decide)
      simpa [RunBound] using hb.trans (straight_replace q 0)

#check transfer_minimum
#print axioms transfer_minimum

end Helicene
```

### `HexagonGraph.lean`

```lean
import HexagonTransfer
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Powerset

namespace Helicene

variable {V : Type*}

def IsMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, ¬ (v ∈ e ∧ v ∈ f)

def IsMaximalMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  IsMatching G M ∧
    ∀ e ∈ G.edgeSet, e ∉ M → ∃ f ∈ M, ∃ v, v ∈ e ∧ v ∈ f

noncomputable def Ψ (G : SimpleGraph V) [Fintype V] : ℕ := by
  classical
  exact (Finset.univ.filter (IsMaximalMatching G)).card

theorem maximal_iff_inclusion (G : SimpleGraph V) (M : Finset (Sym2 V)) :
    IsMaximalMatching G M ↔
      IsMatching G M ∧ ∀ N : Finset (Sym2 V), M ⊆ N → IsMatching G N → N = M := by
  classical
  constructor
  · rintro ⟨hM, hdom⟩
    refine ⟨hM, fun N hs hN => Finset.Subset.antisymm ?_ hs⟩
    intro e he
    by_contra h
    obtain ⟨f, hf, v, hv⟩ := hdom e (hN.1 e he) h
    exact hN.2 e he f (hs hf) (fun h' => h (h'.symm ▸ hf)) v hv
  · rintro ⟨hM, hmax⟩
    refine ⟨hM, fun e he hn => ?_⟩
    by_contra h
    have hi : IsMatching G (insert e M) := by
      refine ⟨?_, ?_⟩
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact he
        · exact hM.1 f hf
      · intro f hf g hg hfg v hv
        rcases Finset.mem_insert.mp hf with heq | hf
        · rcases Finset.mem_insert.mp hg with heq' | hg
          · exact hfg (heq.trans heq'.symm)
          · exact h ⟨g, hg, v, heq ▸ hv⟩
        · rcases Finset.mem_insert.mp hg with heq | hg
          · exact h ⟨f, hf, v, heq ▸ ⟨hv.2, hv.1⟩⟩
          · exact hM.2 f hf g hg hfg v hv
    have he' : e ∈ insert e M := Finset.mem_insert_self e M
    exact hn (hmax _ (Finset.subset_insert _ _) hi ▸ he')

def cycleEdge (f : Vertex → V) (k : Vertex) : Sym2 V :=
  s(f k, f (k+1))

structure BenzenoidChainWitness (G : SimpleGraph V) (n : ℕ) where
  hex : Fin n → (Vertex ↪ V)
  cyc : ∀ i k, G.Adj (hex i k) (hex i (k+1))
  edges_cover : ∀ u v, G.Adj u v → ∃ i k, s(u,v) = cycleEdge (hex i) k
  verts_cover : ∀ v, ∃ i k, hex i k = v
  consec : ∀ (i : Fin n) (h : i.val + 1 < n), ∃ k l : Vertex,
    cycleEdge (hex i) k = cycleEdge (hex ⟨i.val+1, h⟩) l ∧
    ∀ v, v ∈ Set.range (hex i) ∩ Set.range (hex ⟨i.val+1, h⟩) ↔
      v ∈ cycleEdge (hex i) k
  far : ∀ (i j : Fin n), i.val + 1 < j.val →
    Disjoint (Set.range (hex i)) (Set.range (hex j))
  cata : ∀ (i j k : Fin n), i.val + 1 = j.val → j.val + 1 = k.val →
    Disjoint (Set.range (hex i) ∩ Set.range (hex j))
      (Set.range (hex j) ∩ Set.range (hex k))

def chainSize (n : ℕ) : ℕ := 4*n + if n = 0 then 0 else 2

theorem Turn.offset_bounds (t : Turn) : 2 ≤ t.offset.val ∧ t.offset.val ≤ 4 := by
  cases t <;> decide

theorem fin_val_add_one (k : Vertex) (h : k.val ≤ 4) : (k+1).val = k.val+1 := by
  change (k.val + 1) % 6 = k.val + 1
  exact Nat.mod_eq_of_lt (by omega)

def label (t : ℕ → Turn) (i : ℕ) (k : Vertex) : ℕ :=
  if i = 0 ∨ 2 ≤ k.val then 4*i+k.val
  else 4*(i-1)+(t (i-1)).offset.val+(1-k.val)

theorem label_upper (t : ℕ → Turn) (i : ℕ) (k : Vertex) : label t i k ≤ 4*i+5 := by
  have hk := k.isLt
  have ht := (t (i-1)).offset_bounds
  unfold label
  split <;> omega

theorem label_lower (t : ℕ → Turn) (i : ℕ) (k : Vertex) (hi : i ≠ 0) :
    4*(i-1)+2 ≤ label t i k := by
  have ht := (t (i-1)).offset_bounds
  unfold label
  split <;> omega

theorem label_injective (t : ℕ → Turn) (i : ℕ) : Function.Injective (label t i) := by
  intro a b h
  apply Fin.ext
  have ht := (t (i-1)).offset_bounds
  unfold label at h
  split at h <;> split at h <;> omega

def chainHex (t : ℕ → Turn) {n : ℕ} (i : Fin n) : Vertex ↪ Fin (chainSize n) where
  toFun k := ⟨label t i.val k, by
    have hi := i.isLt
    have hu := label_upper t i.val k
    simp only [chainSize, ite_eq_right (show n ≠ 0 by omega)]
    omega⟩
  inj' := fun _ _ h => label_injective t i.val (congrArg Fin.val h)

def chainGraph (t : ℕ → Turn) (n : ℕ) : SimpleGraph (Fin (chainSize n)) where
  Adj a b := ∃ i : Fin n, ∃ k : Vertex, s(a,b) = cycleEdge (chainHex t i) k
  symm := ⟨fun _ _ ⟨i, k, h⟩ => ⟨i, k, Sym2.eq_swap.trans h⟩⟩
  loopless := ⟨fun a ⟨i, k, h⟩ => by
    have hh : chainHex t i k = a := by
      have hm : chainHex t i k ∈ s(a,a) := h.symm ▸ Sym2.mem_mk_left _ _
      simpa [Sym2.mem_iff] using hm
    have hh' : chainHex t i (k+1) = a := by
      have hm : chainHex t i (k+1) ∈ s(a,a) := h.symm ▸ Sym2.mem_mk_right _ _
      simpa [Sym2.mem_iff] using hm
    have hbad := (chainHex t i).injective (hh.trans hh'.symm)
    have hc : ∀ k : Vertex, k ≠ k+1 := by intro v; fin_cases v <;> decide
    exact hc k hbad⟩

theorem chainHex_next (t : ℕ → Turn) {n : ℕ} (i : Fin n) (h : i.val+1<n) :
    chainHex t (⟨i.val+1,h⟩ : Fin n) 0 = chainHex t i ((t i.val).offset+1) ∧
    chainHex t (⟨i.val+1,h⟩ : Fin n) 1 = chainHex t i (t i.val).offset := by
  have hb := (t i.val).offset_bounds
  have hs := fin_val_add_one _ hb.2
  constructor <;> apply Fin.ext
  · change label t (i.val+1) 0 = label t i.val ((t i.val).offset+1)
    simp [label, hs, show 2 ≤ (t i.val).offset.val+1 by omega, Nat.add_assoc]
  · change label t (i.val+1) 1 = label t i.val (t i.val).offset
    simp [label, hb.1]

theorem chainHex_far (t : ℕ → Turn) {n : ℕ} (i j : Fin n) (h : i.val+1<j.val) :
    Disjoint (Set.range (chainHex t i)) (Set.range (chainHex t j)) := by
  rw [Set.disjoint_left]
  rintro v ⟨a, ha⟩ ⟨b, hb⟩
  have hEq : label t i.val a = label t j.val b := congrArg Fin.val (ha.trans hb.symm)
  have hu := label_upper t i.val a
  have hl := label_lower t j.val b (by omega)
  omega

theorem chainHex_cover (t : ℕ → Turn) {n : ℕ} (v : Fin (chainSize n)) :
    ∃ i : Fin n, ∃ k : Vertex, chainHex t i k = v := by
  have hv := v.isLt
  have hn : n ≠ 0 := by
    rintro rfl
    exact Nat.not_lt_zero _ hv
  simp only [chainSize, ite_eq_right hn] at hv
  by_cases h : v.val < 2
  · refine ⟨⟨0, by omega⟩, ⟨v.val, by omega⟩, Fin.ext ?_⟩
    change label t 0 _ = _
    simp [label]
  · let i : Fin n := ⟨(v.val - 2) / 4, by omega⟩
    let k : Vertex := ⟨(v.val - 2) % 4 + 2, by omega⟩
    refine ⟨i, k, Fin.ext ?_⟩
    change label t i.val k = _
    have hk : 2 ≤ k.val := by dsimp [k]; omega
    rw [label, ite_eq_left (Or.inr hk)]
    dsimp [i, k]
    omega

def chainWitness (t : ℕ → Turn) (n : ℕ) : BenzenoidChainWitness (chainGraph t n) n where
  hex := chainHex t
  cyc i k := ⟨i,k,rfl⟩
  edges_cover _ _ h := h
  verts_cover := chainHex_cover t
  consec i h := by
    have hs := chainHex_next t i h
    refine ⟨(t i.val).offset, 0, ?_, ?_⟩
    · change s(_, _) = s(chainHex t (⟨i.val+1,h⟩ : Fin n) 0,
                          chainHex t (⟨i.val+1,h⟩ : Fin n) 1)
      rw [hs.1, hs.2, Sym2.eq_swap]
    · intro v
      change (v ∈ Set.range (chainHex t i) ∧
        v ∈ Set.range (chainHex t (⟨i.val+1,h⟩ : Fin n))) ↔ _
      rw [cycleEdge, Sym2.mem_iff]
      constructor
      · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        have huv := label_upper t i.val a
        have hEq : label t i.val a = label t (i.val+1) b :=
          congrArg Fin.val (ha.trans hb.symm)
        have hb' : b.val < 2 := by
          apply lt_of_not_ge
          intro hbad
          have hval : label t (i.val+1) b = 4*(i.val+1)+b.val := by simp [label, hbad]
          rw [hval] at hEq
          omega
        have hb'' : b = 0 ∨ b = 1 := by
          by_cases hz : b.val = 0
          · exact Or.inl (Fin.ext hz)
          · exact Or.inr (Fin.ext (by change b.val = 1; omega))
        rcases hb'' with rfl | rfl
        · exact Or.inr (hb.symm.trans hs.1)
        · exact Or.inl (hb.symm.trans hs.2)
      · rintro (rfl | rfl)
        · exact ⟨⟨_, rfl⟩, ⟨1, hs.2⟩⟩
        · exact ⟨⟨_, rfl⟩, ⟨0, hs.1⟩⟩
  far := chainHex_far t
  cata i j k hij hjk := by
    rw [Set.disjoint_left]
    intro v hv hw
    exact Set.disjoint_left.mp (chainHex_far t i k (by omega)) hv.1 hw.2

def helicene (n : ℕ) : SimpleGraph (Fin (chainSize n)) :=
  chainGraph (fun _ => .left) n

def heliceneWitness (n : ℕ) : BenzenoidChainWitness (helicene n) n :=
  chainWitness (fun _ => .left) n

#print axioms maximal_iff_inclusion
#print axioms heliceneWitness

end Helicene
```

### `HexagonSlots.lean`

```lean
import HexagonGraph
import Mathlib.Data.Finset.Image

namespace Helicene

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

theorem succ_ne (k : Vertex) : k ≠ k+1 := by fin_cases k <;> decide

theorem cycleEdge_injective (f : Vertex ↪ V) : Function.Injective (cycleEdge f) := by
  intro k l h
  rw [cycleEdge, cycleEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · exact f.injective h.1
  · replace h := And.intro (f.injective h.1) (f.injective h.2)
    have hbad : ∀ k : Vertex, k+1+1 ≠ k := by intro k; fin_cases k <;> decide
    exact (hbad l (by rw [← h.1, h.2])).elim

structure OrientedChain (G : SimpleGraph V) (n : ℕ) extends BenzenoidChainWitness G n where
  turn : Fin n → Turn
  first : ∀ i, i.val = 0 → turn i = .left
  join : ∀ (i : Fin n) (h : i.val+1<n),
    hex ⟨i.val+1,h⟩ 0 = hex i ((turn i).offset+1) ∧
    hex ⟨i.val+1,h⟩ 1 = hex i (turn i).offset

def orientedHelicene (n : ℕ) : OrientedChain (helicene n) n where
  toBenzenoidChainWitness := heliceneWitness n
  turn _ := .left
  first _ _ := rfl
  join := chainHex_next (fun _ => .left)

theorem orientedShared (w : OrientedChain G n) (i : Fin n) (h : i.val+1<n) :
    cycleEdge (w.hex ⟨i.val+1,h⟩) 0 = cycleEdge (w.hex i) (w.turn i).offset := by
  change s(w.hex ⟨i.val+1,h⟩ 0, w.hex ⟨i.val+1,h⟩ 1) = _
  rw [(w.join i h).1, (w.join i h).2, cycleEdge, Sym2.eq_swap]

theorem orientedMeet (w : OrientedChain G n) (i : Fin n) (h : i.val+1<n)
    (v : V) :
    v ∈ Set.range (w.hex i) ∩ Set.range (w.hex ⟨i.val+1,h⟩) ↔
      v ∈ cycleEdge (w.hex ⟨i.val+1,h⟩) 0 := by
  obtain ⟨a, _, _, ha⟩ := w.consec i h
  have hjoin := w.join i h
  have h0 : w.hex ⟨i.val+1,h⟩ 0 ∈ cycleEdge (w.hex i) a :=
    (ha _).mp ⟨⟨_, hjoin.1.symm⟩, ⟨0,rfl⟩⟩
  have h1 : w.hex ⟨i.val+1,h⟩ 1 ∈ cycleEdge (w.hex i) a :=
    (ha _).mp ⟨⟨_, hjoin.2.symm⟩, ⟨1,rfl⟩⟩
  have he := (Sym2.mem_and_mem_iff ((w.hex ⟨i.val+1,h⟩).injective.ne (by decide))).mp ⟨h0,h1⟩
  change cycleEdge (w.hex i) a = cycleEdge (w.hex ⟨i.val+1,h⟩) 0 at he
  rw [← he]
  exact ha v

/-- Only the earlier occurrence of a shared edge owns an edge slot. -/
abbrev OwnedSlot (n : ℕ) := {p : Fin n × Vertex // p.1.val = 0 ∨ p.2 ≠ 0}

def slotEdge (w : OrientedChain G n) (p : OwnedSlot n) : G.edgeSet :=
  ⟨cycleEdge (w.hex p.val.1) p.val.2, w.cyc p.val.1 p.val.2⟩

theorem next_slot_zero (w : OrientedChain G n) (i : Fin n) (h : i.val+1<n)
    (k l : Vertex) (he : cycleEdge (w.hex i) k = cycleEdge (w.hex ⟨i.val+1,h⟩) l) :
    l = 0 := by
  let j : Fin n := ⟨i.val+1,h⟩
  have hmem (a : Vertex) (ha : w.hex j a ∈ cycleEdge (w.hex j) l) :
      w.hex j a ∈ cycleEdge (w.hex j) 0 := by
    apply (orientedMeet w i h _).mp
    refine ⟨?_, ⟨a,rfl⟩⟩
    have ha' : w.hex j a ∈ cycleEdge (w.hex i) k := he.symm ▸ ha
    rw [cycleEdge, Sym2.mem_iff] at ha'
    rcases ha' with ha' | ha'
    · exact ⟨k,ha'.symm⟩
    · exact ⟨k+1,ha'.symm⟩
  have h0 := hmem l (Sym2.mem_mk_left _ _)
  have h1 := hmem (l+1) (Sym2.mem_mk_right _ _)
  have he' := (Sym2.mem_and_mem_iff ((w.hex j).injective.ne (succ_ne l))).mp ⟨h0,h1⟩
  exact cycleEdge_injective (w.hex j) he'.symm

theorem slots_lt_impossible (w : OrientedChain G n) (a b : OwnedSlot n)
    (hlt : a.val.1.val < b.val.1.val)
    (he : cycleEdge (w.hex a.val.1) a.val.2 = cycleEdge (w.hex b.val.1) b.val.2) :
    False := by
  by_cases hfar : a.val.1.val + 1 < b.val.1.val
  · have hmem : w.hex a.val.1 a.val.2 ∈ cycleEdge (w.hex b.val.1) b.val.2 :=
      he ▸ Sym2.mem_mk_left _ _
    rw [cycleEdge, Sym2.mem_iff] at hmem
    apply Set.disjoint_left.mp (w.far a.val.1 b.val.1 hfar)
      ⟨a.val.2,rfl⟩
    rcases hmem with hmem | hmem
    · exact ⟨b.val.2,hmem.symm⟩
    · exact ⟨b.val.2+1,hmem.symm⟩
  · have hj : a.val.1.val+1 < n := by have := b.val.1.isLt; omega
    have hb : b.val.1 = ⟨a.val.1.val+1,hj⟩ := Fin.ext (by change b.val.1.val = a.val.1.val+1; omega)
    have he' : cycleEdge (w.hex a.val.1) a.val.2 =
        cycleEdge (w.hex ⟨a.val.1.val+1,hj⟩) b.val.2 := by rw [← hb]; exact he
    exact b.property.elim (by omega) (fun hb' => hb' (next_slot_zero w a.val.1 hj _ _ he'))

theorem slotEdge_injective (w : OrientedChain G n) : Function.Injective (slotEdge w) := by
  intro a b h
  have he : cycleEdge (w.hex a.val.1) a.val.2 = cycleEdge (w.hex b.val.1) b.val.2 :=
    congrArg Subtype.val h
  rcases lt_trichotomy a.val.1.val b.val.1.val with hlt | heq | hgt
  · exact (slots_lt_impossible w a b hlt he).elim
  · apply Subtype.ext
    have hface : a.val.1 = b.val.1 := Fin.ext heq
    apply Prod.ext hface
    rw [hface] at he
    exact cycleEdge_injective (w.hex b.val.1) he
  · exact (slots_lt_impossible w b a hgt he.symm).elim

theorem slotEdge_surjective (w : OrientedChain G n) : Function.Surjective (slotEdge w) := by
  rintro ⟨e,he⟩
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨i,k,hik⟩ := w.edges_cover a b he
    by_cases hs : i.val = 0 ∨ k ≠ 0
    · exact ⟨⟨(i,k),hs⟩, Subtype.ext hik.symm⟩
    · have hi : i.val ≠ 0 := fun hi => hs (Or.inl hi)
      have hk : k = 0 := not_not.mp (fun hk => hs (Or.inr hk))
      subst k
      have hj : i.val-1 < n := by have := i.isLt; omega
      let j : Fin n := ⟨i.val-1,hj⟩
      have hnext : j.val+1<n := by have := i.isLt; change i.val-1+1<n; omega
      have heq : (⟨j.val+1,hnext⟩ : Fin n) = i := Fin.ext (by change i.val-1+1=i.val; omega)
      have hb := (w.turn j).offset_bounds.1
      have hne : (w.turn j).offset ≠ 0 := by
        intro h
        rw [h] at hb
        exact (by decide : ¬ 2 ≤ (0 : Vertex).val) hb
      refine ⟨⟨(j,(w.turn j).offset),Or.inr hne⟩, Subtype.ext ?_⟩
      change cycleEdge (w.hex j) (w.turn j).offset = s(a,b)
      rw [← orientedShared w j hnext, heq, hik]

noncomputable def edgeSlots (w : OrientedChain G n) : OwnedSlot n ≃ G.edgeSet :=
  Equiv.ofBijective (slotEdge w) ⟨slotEdge_injective w, slotEdge_surjective w⟩

#print axioms orientedHelicene
#print axioms edgeSlots

end Helicene
```

### `HexagonOrientation.lean`

```lean
import HexagonSlots

namespace Helicene

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

def indexAt (a : Vertex) (flip : Bool) (k : Vertex) : Vertex :=
  if flip then a-k else a+k

theorem indexAt_inverse (a : Vertex) (flip : Bool) (k : Vertex) :
    indexAt (if flip then a else 0-a) flip (indexAt a flip k) = k := by
  cases flip <;> fin_cases a <;> fin_cases k <;> decide

theorem indexAt_inverse' (a : Vertex) (flip : Bool) (k : Vertex) :
    indexAt a flip (indexAt (if flip then a else 0-a) flip k) = k := by
  cases flip <;> fin_cases a <;> fin_cases k <;> decide

def reindex (a : Vertex) (flip : Bool) : Vertex ≃ Vertex where
  toFun := indexAt a flip
  invFun := indexAt (if flip then a else 0-a) flip
  left_inv := indexAt_inverse a flip
  right_inv := indexAt_inverse' a flip

structure CycleFrame (f : Vertex ↪ V) where
  hex : Vertex ↪ V
  range_eq : Set.range hex = Set.range f
  edges_eq : Set.range (cycleEdge hex) = Set.range (cycleEdge f)

theorem transitionIndex (a : Vertex) (flip : Bool) (k : Vertex) :
    let j := indexAt (if flip then a-1 else a) flip k
    (indexAt a flip k = j ∧ indexAt a flip (k+1) = j+1) ∨
    (indexAt a flip k = j+1 ∧ indexAt a flip (k+1) = j) := by
  cases flip <;> fin_cases a <;> fin_cases k <;> decide

def dihedralFrame (f : Vertex ↪ V) (a : Vertex) (flip : Bool) : CycleFrame f where
  hex := (reindex a flip).toEmbedding.trans f
  range_eq := by
    ext v
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨indexAt a flip k,rfl⟩
    · rintro ⟨k,rfl⟩
      exact ⟨(reindex a flip).symm k, congrArg f ((reindex a flip).apply_symm_apply k)⟩
  edges_eq := by
    let e := reindex (if flip then a-1 else a) flip
    have he (k : Vertex) :
        cycleEdge ((reindex a flip).toEmbedding.trans f) k = cycleEdge f (e k) := by
      change s(f (indexAt a flip k), f (indexAt a flip (k+1))) = s(f (e k), f (e k+1))
      rcases transitionIndex a flip k with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · rw [h₁,h₂]; rfl
      · rw [h₁,h₂,Sym2.eq_swap]; rfl
    ext z
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨e k,(he k).symm⟩
    · rintro ⟨k,rfl⟩
      exact ⟨e.symm k, (he _).trans (congrArg (cycleEdge f) (e.apply_symm_apply k))⟩

theorem frameIncoming (f : Vertex ↪ V) (l : Vertex) (u v : V)
    (h : s(u,v) = cycleEdge f l) :
    ∃ a : CycleFrame f, a.hex 0 = u ∧ a.hex 1 = v := by
  rw [cycleEdge, Sym2.eq_iff] at h
  rcases h with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · refine ⟨dihedralFrame f l false, ?_, ?_⟩
    · change f (indexAt l false 0) = u
      rw [h0]
      exact congrArg f (by fin_cases l <;> decide)
    · exact h1.symm
  · refine ⟨dihedralFrame f (l+1) true, ?_, ?_⟩
    · change f (indexAt (l+1) true 0) = u
      rw [h0]
      exact congrArg f (by fin_cases l <;> decide)
    · change f (indexAt (l+1) true 1) = v
      rw [h1]
      exact congrArg f (by fin_cases l <;> decide)

structure FramedFace (w : BenzenoidChainWitness G n) (i : Fin n) where
  frame : CycleFrame (w.hex i)
  turn : Turn
  first : i.val = 0 → turn = .left
  outgoing : ∀ (h : i.val+1<n), ∃ l : Vertex,
    cycleEdge frame.hex turn.offset = cycleEdge (w.hex ⟨i.val+1,h⟩) l

theorem firstFrame (w : BenzenoidChainWitness G n) (i : Fin n) (_hi : i.val = 0) :
    Nonempty (FramedFace w i) := by
  by_cases hh : i.val+1<n
  · obtain ⟨k,l,hkl,_⟩ := w.consec i hh
    refine ⟨⟨dihedralFrame (w.hex i) (k-2) false, .left, fun _ => rfl, fun h => ⟨l,?_⟩⟩⟩
    have he (p : Vertex) : indexAt (p-2) false 2 = p ∧ indexAt (p-2) false 3 = p+1 := by
      fin_cases p <;> decide
    exact (congrArg₂ (fun a b => s(w.hex i a,w.hex i b)) (he k).1 (he k).2).trans hkl
  · exact ⟨⟨dihedralFrame (w.hex i) 0 false, .left, fun _ => rfl,
      fun h => (hh h).elim⟩⟩

theorem offset_of_disjoint (k : Vertex) (h0 : k ≠ 0) (h1 : k ≠ 1)
    (h5 : k+1 ≠ 0) : ∃ t : Turn, t.offset = k := by
  fin_cases k
  · exact (h0 rfl).elim
  · exact (h1 rfl).elim
  · exact ⟨.left,rfl⟩
  · exact ⟨.straight,rfl⟩
  · exact ⟨.right,rfl⟩
  · exact (h5 rfl).elim

theorem frameNext (w : BenzenoidChainWitness G n) (i : Fin n) (hi : i.val+1<n)
    (p : FramedFace w i) :
    ∃ q : FramedFace w ⟨i.val+1,hi⟩,
      q.frame.hex 0 = p.frame.hex (p.turn.offset+1) ∧
      q.frame.hex 1 = p.frame.hex p.turn.offset := by
  let j : Fin n := ⟨i.val+1,hi⟩
  obtain ⟨l, hl⟩ := p.outgoing hi
  obtain ⟨f, h0, h1⟩ := frameIncoming (w.hex j) l
    (p.frame.hex (p.turn.offset+1)) (p.frame.hex p.turn.offset) (Sym2.eq_swap.trans hl)
  by_cases hj : j.val+1<n
  · obtain ⟨k,m,hm,_⟩ := w.consec j hj
    have hmem : cycleEdge (w.hex j) k ∈ Set.range (cycleEdge f.hex) :=
      f.edges_eq.symm ▸ ⟨k,rfl⟩
    obtain ⟨k', hk'⟩ := hmem
    have hm' : cycleEdge f.hex k' = cycleEdge (w.hex ⟨j.val+1,hj⟩) m := hk'.trans hm
    have hdis := w.far i ⟨j.val+1,hj⟩ (by change i.val+1<i.val+1+1; omega)
    have hPrev (r : Vertex) : p.frame.hex r ∈ Set.range (w.hex i) :=
      p.frame.range_eq ▸ ⟨r,rfl⟩
    have hNext (a : Vertex) (ha : f.hex a ∈ cycleEdge f.hex k') :
        f.hex a ∈ Set.range (w.hex ⟨j.val+1,hj⟩) := by
      rw [hm', cycleEdge, Sym2.mem_iff] at ha
      rcases ha with ha | ha
      · exact ⟨m,ha.symm⟩
      · exact ⟨m+1,ha.symm⟩
    have hbad0 : ¬ f.hex 0 ∈ Set.range (w.hex ⟨j.val+1,hj⟩) :=
      fun hv => Set.disjoint_left.mp hdis (h0.symm ▸ hPrev _) hv
    have hbad1 : ¬ f.hex 1 ∈ Set.range (w.hex ⟨j.val+1,hj⟩) :=
      fun hv => Set.disjoint_left.mp hdis (h1.symm ▸ hPrev _) hv
    obtain ⟨t,ht⟩ := offset_of_disjoint k'
      (fun h => hbad0 (h ▸ hNext k' (Sym2.mem_mk_left _ _)))
      (fun h => hbad1 (h ▸ hNext k' (Sym2.mem_mk_left _ _)))
      (fun h => hbad0 (h ▸ hNext (k'+1) (Sym2.mem_mk_right _ _)))
    refine ⟨⟨f,t,fun h => ?_,fun h => ⟨m,?_⟩⟩, h0,h1⟩
    · change i.val+1=0 at h
      omega
    · rw [ht]
      exact hm'
  · refine ⟨⟨f,.left,fun _ => rfl,fun h => (hj h).elim⟩,h0,h1⟩

noncomputable def frames (w : BenzenoidChainWitness G n) :
    (i : ℕ) → (hi : i<n) → FramedFace w ⟨i,hi⟩
  | 0, hi => Classical.choice (firstFrame w ⟨0,hi⟩ rfl)
  | i+1, hi => Classical.choose (frameNext w ⟨i,by omega⟩ hi (frames w i (by omega)))

theorem frames_join (w : BenzenoidChainWitness G n) (i : Fin n) (hi : i.val+1<n) :
    let a := frames w i.val i.isLt
    let b := frames w (i.val+1) hi
    b.frame.hex 0 = a.frame.hex (a.turn.offset+1) ∧
    b.frame.hex 1 = a.frame.hex a.turn.offset := by
  change (frames w (i.val+1) hi).frame.hex 0 = _ ∧ _
  rw [frames]
  exact Classical.choose_spec (frameNext w i hi (frames w i.val i.isLt))

noncomputable def orient (w : BenzenoidChainWitness G n) : OrientedChain G n where
  hex i := (frames w i.val i.isLt).frame.hex
  cyc i k := by
    let f := (frames w i.val i.isLt).frame
    have hm : cycleEdge f.hex k ∈ Set.range (cycleEdge (w.hex i)) :=
      f.edges_eq ▸ ⟨k,rfl⟩
    obtain ⟨l,hl⟩ := hm
    exact (show cycleEdge f.hex k ∈ G.edgeSet from hl ▸ w.cyc i l)
  edges_cover u v huv := by
    obtain ⟨i,k,he⟩ := w.edges_cover u v huv
    let f := (frames w i.val i.isLt).frame
    have hm : s(u,v) ∈ Set.range (cycleEdge f.hex) :=
      f.edges_eq.symm ▸ ⟨k,he.symm⟩
    obtain ⟨l,hl⟩ := hm
    exact ⟨i,l,hl.symm⟩
  verts_cover v := by
    obtain ⟨i,k,he⟩ := w.verts_cover v
    let f := (frames w i.val i.isLt).frame
    obtain ⟨l,hl⟩ : v ∈ Set.range f.hex := f.range_eq.symm ▸ ⟨k,he⟩
    exact ⟨i,l,hl⟩
  consec i h := by
    let j : Fin n := ⟨i.val+1,h⟩
    let f := (frames w i.val i.isLt).frame
    let g := (frames w j.val j.isLt).frame
    obtain ⟨k,l,he,hm⟩ := w.consec i h
    obtain ⟨a,ha⟩ : cycleEdge (w.hex i) k ∈ Set.range (cycleEdge f.hex) :=
      f.edges_eq.symm ▸ ⟨k,rfl⟩
    obtain ⟨b,hb⟩ : cycleEdge (w.hex j) l ∈ Set.range (cycleEdge g.hex) :=
      g.edges_eq.symm ▸ ⟨l,rfl⟩
    refine ⟨a,b,ha.trans (he.trans hb.symm),fun v => ?_⟩
    change v ∈ Set.range f.hex ∩ Set.range g.hex ↔ v ∈ cycleEdge f.hex a
    rw [f.range_eq,g.range_eq,ha]
    exact hm v
  far i j hij := by
    rw [(frames w i.val i.isLt).frame.range_eq,(frames w j.val j.isLt).frame.range_eq]
    exact w.far i j hij
  cata i j k hij hjk := by
    rw [(frames w i.val i.isLt).frame.range_eq,(frames w j.val j.isLt).frame.range_eq,
      (frames w k.val k.isLt).frame.range_eq]
    exact w.cata i j k hij hjk
  turn i := (frames w i.val i.isLt).turn
  first i := (frames w i.val i.isLt).first
  join := frames_join w

#print axioms orient

end Helicene
```

### `HexagonChoices.lean`

```lean
import HexagonSlots

namespace Helicene

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

abbrev GraphEdgeSubsets (G : SimpleGraph V) :=
  {M : Finset (Sym2 V) // ∀ e ∈ M, e ∈ G.edgeSet}

def NoRepeatedEdges (c : Fin n → Choice) : Prop :=
  ∀ i : Fin n, i.val ≠ 0 → c i 0 = false

def slotEmbedding (w : OrientedChain G n) : OwnedSlot n ↪ Sym2 V where
  toFun p := (slotEdge w p).val
  inj' _ _ h := slotEdge_injective w (Subtype.ext h)

noncomputable def chosenEdges (w : OrientedChain G n) (c : Fin n → Choice) :
    GraphEdgeSubsets G := by
  classical
  refine ⟨(Finset.univ.filter fun p : OwnedSlot n => c p.val.1 p.val.2 = true).map
    (slotEmbedding w), ?_⟩
  intro e he
  obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp he
  exact (slotEdge w p).property

theorem mem_chosenEdges (w : OrientedChain G n) (c : Fin n → Choice) (p : OwnedSlot n) :
    (slotEdge w p).val ∈ (chosenEdges w c).val ↔ c p.val.1 p.val.2 = true := by
  classical
  change slotEmbedding w p ∈ (chosenEdges w c).val ↔ _
  simp [chosenEdges]

theorem chosenEdges_iff (w : OrientedChain G n) (c : Fin n → Choice) (e : Sym2 V) :
    e ∈ (chosenEdges w c).val ↔
      ∃ p : OwnedSlot n, c p.val.1 p.val.2 = true ∧ (slotEdge w p).val = e := by
  classical
  simp only [chosenEdges, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

noncomputable def edgeChoices (w : OrientedChain G n) (M : GraphEdgeSubsets G)
    (i : Fin n) (k : Vertex) : Bool := by
  classical
  exact decide ((i.val = 0 ∨ k ≠ 0) ∧ cycleEdge (w.hex i) k ∈ M.val)

theorem edgeChoices_iff (w : OrientedChain G n) (M : GraphEdgeSubsets G)
    (i : Fin n) (k : Vertex) :
    edgeChoices w M i k = true ↔
      (i.val = 0 ∨ k ≠ 0) ∧ cycleEdge (w.hex i) k ∈ M.val := by
  classical
  unfold edgeChoices
  simp

theorem edgeChoices_owned (w : OrientedChain G n) (M : GraphEdgeSubsets G) :
    NoRepeatedEdges (edgeChoices w M) := by
  intro i hi
  cases h : edgeChoices w M i 0
  · rfl
  · exact ((edgeChoices_iff w M i 0).mp h).1.elim (fun h0 => (hi h0).elim)
      (fun h0 => (h0 rfl).elim)

noncomputable def matchingChoices (w : OrientedChain G n) :
    GraphEdgeSubsets G ≃ { c : Fin n → Choice // NoRepeatedEdges c } where
  toFun M := ⟨edgeChoices w M, edgeChoices_owned w M⟩
  invFun c := chosenEdges w c.val
  left_inv M := by
    classical
    apply Subtype.ext
    ext e
    constructor
    · intro he
      obtain ⟨p,hp,hpe⟩ := (chosenEdges_iff w _ e).mp he
      exact hpe ▸ ((edgeChoices_iff w M p.val.1 p.val.2).mp hp).2
    · intro he
      obtain ⟨p,hp⟩ := slotEdge_surjective w ⟨e,M.property e he⟩
      have hpe := congrArg Subtype.val hp
      refine (chosenEdges_iff w _ e).mpr ⟨p,?_,hpe⟩
      apply (edgeChoices_iff w M _ _).mpr
      refine ⟨p.property,?_⟩
      change (slotEdge w p).val ∈ M.val
      rw [hpe]
      exact he
  right_inv c := by
    apply Subtype.ext
    funext i k
    apply Bool.eq_iff_iff.mpr
    rw [edgeChoices_iff]
    by_cases h : i.val = 0 ∨ k ≠ 0
    · rw [show (i.val = 0 ∨ k ≠ 0) = True from propext (iff_true_intro h), true_and]
      exact mem_chosenEdges w c.val ⟨(i,k),h⟩
    · have hz : k = 0 := not_not.mp (fun hk => h (Or.inr hk))
      subst k
      have hc := c.property i (fun hi => h (Or.inl hi))
      exact ⟨fun hh => (h hh.1).elim, fun hh => by rw [hc] at hh; contradiction⟩

theorem family_mem_edge (w : OrientedChain G n) (c : Fin n → Choice)
    (hc : NoRepeatedEdges c) (i : Fin n) (k : Vertex) :
    c i k = true → cycleEdge (w.hex i) k ∈ (chosenEdges w c).val := by
  intro h
  have hown : i.val = 0 ∨ k ≠ 0 := by
    by_cases hi : i.val = 0
    · exact Or.inl hi
    · refine Or.inr (fun hk => ?_)
      subst k
      rw [hc i hi] at h
      contradiction
  exact (mem_chosenEdges w c ⟨(i,k),hown⟩).mpr h

theorem chosen_has_vertex (w : OrientedChain G n) (c : Fin n → Choice)
    (hc : NoRepeatedEdges c) (v : V) :
    (∃ e ∈ (chosenEdges w c).val, v ∈ e) ↔
      ∃ (i : Fin n) (k : Vertex), c i k = true ∧ v ∈ cycleEdge (w.hex i) k := by
  constructor
  · rintro ⟨e,he,hv⟩
    obtain ⟨p,hp,hpe⟩ := (chosenEdges_iff w c e).mp he
    refine ⟨p.val.1,p.val.2,hp,?_⟩
    change v ∈ (slotEdge w p).val
    rw [hpe]
    exact hv
  · rintro ⟨i,k,hk,hv⟩
    exact ⟨_,family_mem_edge w c hc i k hk,hv⟩

#print axioms matchingChoices

end Helicene
```

### `HexagonIncidence.lean`

```lean
import HexagonChoices

namespace Helicene

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

def Hits (w : OrientedChain G n) (c : Fin n → Choice) (i : Fin n) (v : V) : Prop :=
  ∃ k : Vertex, c i k = true ∧ v ∈ cycleEdge (w.hex i) k

def Covered (w : OrientedChain G n) (c : Fin n → Choice) (v : V) : Prop :=
  ∃ i, Hits w c i v

theorem hits_range {w : OrientedChain G n} {c : Fin n → Choice} {i : Fin n}
    {v : V} (h : Hits w c i v) : v ∈ Set.range (w.hex i) := by
  obtain ⟨k,_,hk⟩ := h
  rw [cycleEdge, Sym2.mem_iff] at hk
  rcases hk with hk | hk
  · exact ⟨k,hk.symm⟩
  · exact ⟨k+1,hk.symm⟩

theorem vertex_sub_add (k : Vertex) : k-1+1=k := by fin_cases k <;> decide
theorem vertex_add_sub (k : Vertex) : k+1-1=k := by fin_cases k <;> decide
theorem vertex_sub_ne (k : Vertex) : k ≠ k-1 := by fin_cases k <;> decide

theorem hits_iff_touched (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (k : Vertex) : Hits w c i (w.hex i k) ↔ touched (c i) k = true := by
  rw [touched, Bool.or_eq_true]
  constructor
  · rintro ⟨l,hl,hm⟩
    rw [cycleEdge, Sym2.mem_iff] at hm
    rcases hm with h | h
    · exact Or.inl ((w.hex i).injective h ▸ hl)
    · have he : k-1=l := by rw [(w.hex i).injective h, vertex_add_sub]
      exact Or.inr (he ▸ hl)
  · rintro (h | h)
    · exact ⟨k,h,Sym2.mem_mk_left _ _⟩
    · refine ⟨k-1,h,?_⟩
      rw [cycleEdge, vertex_sub_add]
      exact Sym2.mem_mk_right _ _

theorem hit_faces_close {w : OrientedChain G n} {c : Fin n → Choice}
    {i j : Fin n} {v : V} (hi : v ∈ Set.range (w.hex i)) (hj : Hits w c j v) :
    i.val ≤ j.val+1 ∧ j.val ≤ i.val+1 := by
  constructor
  · by_contra! hh
    exact Set.disjoint_left.mp (w.far j i hh) (hits_range hj) hi
  · by_contra! hh
    exact Set.disjoint_left.mp (w.far i j hh) hi (hits_range hj)

theorem local_collision {f : Vertex ↪ V} {c : Choice}
    (h : ∀ k, ¬ (c k = true ∧ c (k-1) = true))
    {a b : Vertex} (ha : c a = true) (hb : c b = true) {v : V}
    (hv : v ∈ cycleEdge f a ∧ v ∈ cycleEdge f b) : a = b := by
  rw [cycleEdge, cycleEdge, Sym2.mem_iff, Sym2.mem_iff] at hv
  rcases hv with ⟨ha' | ha', hb' | hb'⟩
  · exact f.injective (ha'.symm.trans hb')
  · have he : a = b+1 := f.injective (ha'.symm.trans hb')
    have he' : a-1 = b := by rw [he, vertex_add_sub]
    exact (h a ⟨ha,he' ▸ hb⟩).elim
  · have he : b = a+1 := f.injective (hb'.symm.trans ha')
    have he' : b-1 = a := by rw [he, vertex_add_sub]
    exact (h b ⟨hb,he' ▸ ha⟩).elim
  · have he : a+1 = b+1 := f.injective (ha'.symm.trans hb')
    simpa only [vertex_add_sub] using congrArg (· - (1 : Vertex)) he

theorem choice_owned {c : Fin n → Choice} (hc : NoRepeatedEdges c)
    {i : Fin n} {k : Vertex} (h : c i k = true) : i.val = 0 ∨ k ≠ 0 := by
  by_cases hi : i.val = 0
  · exact Or.inl hi
  · refine Or.inr fun he => ?_
    subst k
    rw [hc i hi] at h
    contradiction

theorem matching_iff_local (w : OrientedChain G n) (c : Fin n → Choice)
    (hc : NoRepeatedEdges c) :
    IsMatching G (chosenEdges w c).val ↔
      (∀ i k, ¬ (c i k = true ∧ c i (k-1) = true)) ∧
      (∀ (i j : Fin n), i.val+1=j.val → ∀ v, ¬ (Hits w c i v ∧ Hits w c j v)) := by
  constructor
  · intro h
    constructor
    · rintro i k ⟨h₁,h₂⟩
      have he : cycleEdge (w.hex i) k ≠ cycleEdge (w.hex i) (k-1) :=
        (cycleEdge_injective (w.hex i)).ne (vertex_sub_ne k)
      exact h.2 _ (family_mem_edge w c hc i k h₁)
        _ (family_mem_edge w c hc i (k-1) h₂) he (w.hex i k)
        ⟨Sym2.mem_mk_left _ _, by rw [cycleEdge, vertex_sub_add]; exact Sym2.mem_mk_right _ _⟩
    · rintro i j hij v ⟨⟨a,ha,hva⟩,⟨b,hb,hvb⟩⟩
      have he : cycleEdge (w.hex i) a ≠ cycleEdge (w.hex j) b := by
        intro he
        exact slots_lt_impossible w ⟨(i,a),choice_owned hc ha⟩
          ⟨(j,b),choice_owned hc hb⟩ (by change i.val<j.val; omega) he
      exact h.2 _ (family_mem_edge w c hc i a ha)
        _ (family_mem_edge w c hc j b hb) he v ⟨hva,hvb⟩
  · rintro ⟨hl,hcross⟩
    refine ⟨(chosenEdges w c).property,?_⟩
    rintro e he f hf hne v ⟨hve,hvf⟩
    obtain ⟨p,hp,hpe⟩ := (chosenEdges_iff w c e).mp he
    obtain ⟨q,hq,hqf⟩ := (chosenEdges_iff w c f).mp hf
    subst e
    subst f
    let i := p.val.1
    let j := q.val.1
    have hvi : Hits w c i v := ⟨p.val.2,hp,hve⟩
    have hvj : Hits w c j v := ⟨q.val.2,hq,hvf⟩
    have hdiff := hit_faces_close (hits_range hvi) hvj
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact hcross i j (by omega) v ⟨hvi,hvj⟩
    · have heq' : p.val.1 = q.val.1 := Fin.ext heq
      apply hne
      change cycleEdge (w.hex p.val.1) p.val.2 = cycleEdge (w.hex q.val.1) q.val.2
      change v ∈ cycleEdge (w.hex p.val.1) p.val.2 at hve
      have h' : c p.val.1 q.val.2 = true := heq'.symm ▸ hq
      have hv' : v ∈ cycleEdge (w.hex p.val.1) q.val.2 := heq'.symm ▸ hvf
      have hk := local_collision (hl p.val.1) hp h' ⟨hve,hv'⟩
      rw [hk,heq']
    · exact hcross j i (by omega) v ⟨hvj,hvi⟩

theorem maximal_iff_local (w : OrientedChain G n) (c : Fin n → Choice)
    (hc : NoRepeatedEdges c) :
    IsMaximalMatching G (chosenEdges w c).val ↔
      (∀ i k, ¬ (c i k = true ∧ c i (k-1) = true)) ∧
      (∀ (i j : Fin n), i.val+1=j.val → ∀ v, ¬ (Hits w c i v ∧ Hits w c j v)) ∧
      (∀ i k, Covered w c (w.hex i k) ∨ Covered w c (w.hex i (k+1))) := by
  have hv (v : V) :
      Covered w c v ↔ ∃ e ∈ (chosenEdges w c).val, v ∈ e :=
    (chosen_has_vertex w c hc v).symm
  constructor
  · intro h
    obtain ⟨hl,hcross⟩ := (matching_iff_local w c hc).mp h.1
    refine ⟨hl,hcross,fun i k => ?_⟩
    by_cases he : cycleEdge (w.hex i) k ∈ (chosenEdges w c).val
    · exact Or.inl ((hv _).mpr ⟨_,he,Sym2.mem_mk_left _ _⟩)
    · obtain ⟨e,he',v,hv',hve⟩ := h.2 _ (w.cyc i k) he
      rw [cycleEdge, Sym2.mem_iff] at hv'
      rcases hv' with h₀ | h₁
      · exact Or.inl ((hv _).mpr ⟨e,he',h₀ ▸ hve⟩)
      · exact Or.inr ((hv _).mpr ⟨e,he',h₁ ▸ hve⟩)
  · rintro ⟨hl,hcross,hdom⟩
    refine ⟨(matching_iff_local w c hc).mpr ⟨hl,hcross⟩,?_⟩
    intro e he _
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨i,k,hk⟩ := w.edges_cover a b he
      rw [hk]
      rcases hdom i k with huv | huv
      · obtain ⟨f,hf,hfv⟩ := (hv _).mp huv
        exact ⟨f,hf,_,Sym2.mem_mk_left _ _,hfv⟩
      · obtain ⟨f,hf,hfv⟩ := (hv _).mp huv
        exact ⟨f,hf,_,Sym2.mem_mk_right _ _,hfv⟩

#print axioms maximal_iff_local

end Helicene
```

### `HexagonBoundary.lean`

```lean
import HexagonIncidence

namespace Helicene

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

def outgoing (w : OrientedChain G n) (i : Fin n) : Option Turn :=
  if i.val+1<n then some (w.turn i) else none

theorem port_some (t : Turn) (k : Vertex) :
    port (some t) k = true ↔ k = t.offset ∨ k = t.offset+1 := by
  simp [port]

theorem port_iff_later (w : OrientedChain G n) (i : Fin n) (k : Vertex) :
    port (outgoing w i) k = true ↔
      ∃ j : Fin n, i.val < j.val ∧ w.hex i k ∈ Set.range (w.hex j) := by
  unfold outgoing
  split
  next hi =>
    rw [port_some]
    constructor
    · intro he
      refine ⟨⟨i.val+1,hi⟩,by change i.val<i.val+1; omega,?_⟩
      rcases he with rfl | rfl
      · exact ⟨1,(w.join i hi).2⟩
      · exact ⟨0,(w.join i hi).1⟩
    · rintro ⟨j,hj,hm⟩
      have hself : w.hex i k ∈ Set.range (w.hex i) := ⟨k,rfl⟩
      have hg : ¬ i.val+1<j.val := by
        intro h
        exact Set.disjoint_left.mp (w.far i j h) hself hm
      have hj' : j = ⟨i.val+1,hi⟩ := Fin.ext (by change j.val=i.val+1; omega)
      subst j
      have he := (orientedMeet w i hi _).mp ⟨hself,hm⟩
      rw [orientedShared,cycleEdge,Sym2.mem_iff] at he
      exact he.elim (fun h => Or.inl ((w.hex i).injective h))
        (fun h => Or.inr ((w.hex i).injective h))
  next hi =>
    simp only [port, Bool.false_eq_true, false_iff]
    rintro ⟨j,hj,_⟩
    have := j.isLt
    omega

theorem incoming_vertex (w : OrientedChain G n) (i : Fin n) (hi : i.val+1<n)
    (k : Vertex) :
    w.hex ⟨i.val+1,hi⟩ k ∈ Set.range (w.hex i) ↔ k = 0 ∨ k = 1 := by
  have h (v : V) := orientedMeet w i hi v
  constructor
  · intro hs
    have he := (h _).mp ⟨hs,⟨k,rfl⟩⟩
    change w.hex ⟨i.val+1,hi⟩ k ∈
      s(w.hex ⟨i.val+1,hi⟩ 0,w.hex ⟨i.val+1,hi⟩ 1) at he
    rw [Sym2.mem_iff] at he
    exact he.elim (fun h => Or.inl ((w.hex _).injective h))
      (fun h => Or.inr ((w.hex _).injective h))
  · rintro (rfl | rfl)
    · exact ⟨_,(w.join i hi).1.symm⟩
    · exact ⟨_,(w.join i hi).2.symm⟩

theorem incoming_forgotten (w : OrientedChain G n) (i : Fin n) (hi : i.val+1<n)
    (k : Vertex) (hk : k = 0 ∨ k = 1) :
    port (outgoing w ⟨i.val+1,hi⟩) k = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨j,hj,hv⟩ := (port_iff_later w _ k).mp h
  have hfar : i.val+1<j.val := hj
  exact Set.disjoint_left.mp (w.far i j hfar) ((incoming_vertex w i hi k).mpr hk) hv

def stateAt (w : OrientedChain G n) (c : Fin n → Choice) :
    (i : ℕ) → i<n → Option State
  | 0, _ => none
  | i+1, h => some (outputState (stateAt w c i (by omega))
      (w.turn ⟨i,by omega⟩) (c ⟨i,by omega⟩))

def incoming (w : OrientedChain G n) (c : Fin n → Choice) (i : Fin n) : Option State :=
  stateAt w c i.val i.isLt

theorem incoming_initial (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (hi : i.val=0) : incoming w c i = none := by
  obtain ⟨i,hi'⟩ := i
  change i=0 at hi
  subst i
  rfl

theorem incoming_next (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (hi : i.val+1<n) :
    incoming w c ⟨i.val+1,hi⟩ = some (outputState (incoming w c i) (w.turn i) (c i)) := rfl

theorem incoming_some (w : OrientedChain G n) (c : Fin n → Choice) (i : Fin n)
    (hi : i.val ≠ 0) : (incoming w c i).isSome := by
  obtain ⟨i,hi'⟩ := i
  cases i with
  | zero => exact (hi rfl).elim
  | succ i => rfl

theorem front_state_zero (a b : Status) : frontStatus (state a b) 0 = a := by
  fin_cases a <;> fin_cases b <;> decide

theorem front_state_one (a b : Status) : frontStatus (state a b) 1 = b := by
  fin_cases a <;> fin_cases b <;> decide

theorem prior_nonport (a : Option State) (k : Vertex) (h₀ : k ≠ 0) (h₁ : k ≠ 1) :
    prior a k = 0 := by
  cases a <;> simp [prior,frontStatus,h₀,h₁]

theorem offset_ne (t : Turn) : t.offset ≠ 0 ∧ t.offset ≠ 1 ∧
    t.offset+1 ≠ 0 ∧ t.offset+1 ≠ 1 := by cases t <;> decide

theorem matched_offset (a : Option State) (t : Turn) (c : Choice) :
    matched a c t.offset = touched c t.offset ∧
    matched a c (t.offset+1) = touched c (t.offset+1) := by
  have hh := offset_ne t
  constructor
  · simp [matched, prior_nonport a _ hh.1 hh.2.1]
  · simp [matched, prior_nonport a _ hh.2.2.1 hh.2.2.2]

def outputStatus (a : Option State) (t : Turn) (c : Choice) (k : Vertex) : Status :=
  if matched a c k then 1 else if required a (some t) c k then 2 else 0

theorem prior_next_zero (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (hi : i.val+1<n) :
    prior (incoming w c ⟨i.val+1,hi⟩) 0 =
      outputStatus (incoming w c i) (w.turn i) (c i) ((w.turn i).offset+1) := by
  rw [incoming_next]
  exact front_state_zero _ _

theorem prior_next_one (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (hi : i.val+1<n) :
    prior (incoming w c ⟨i.val+1,hi⟩) 1 =
      outputStatus (incoming w c i) (w.turn i) (c i) (w.turn i).offset := by
  rw [incoming_next]
  exact front_state_one _ _

theorem outputStatus_matched (a : Option State) (t : Turn) (c : Choice) (k : Vertex) :
    outputStatus a t c k = 1 ↔ matched a c k = true := by
  cases hm : matched a c k <;> cases hr : required a (some t) c k <;>
    simp [outputStatus,hm,hr]

theorem outputStatus_required (a : Option State) (t : Turn) (c : Choice) (k : Vertex) :
    outputStatus a t c k = 2 ↔ required a (some t) c k = true := by
  cases hm : matched a c k
  · cases hr : required a (some t) c k <;> simp [outputStatus,hm,hr]
  · have hr : required a (some t) c k = false := by simp [required,hm]
    simp [outputStatus,hm,hr]

theorem prior_one_next (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (hi : i.val+1<n) (k : Vertex) :
    prior (incoming w c ⟨i.val+1,hi⟩) k = 1 ↔ Hits w c i (w.hex ⟨i.val+1,hi⟩ k) := by
  by_cases h₀ : k=0
  · subst k
    rw [prior_next_zero, outputStatus_matched, (matched_offset _ _ _).2,
      (w.join i hi).1, hits_iff_touched]
  · by_cases h₁ : k=1
    · subst k
      rw [prior_next_one, outputStatus_matched, (matched_offset _ _ _).1,
        (w.join i hi).2, hits_iff_touched]
    · rw [prior_nonport _ _ h₀ h₁]
      constructor
      · intro h
        exact ((by decide : (0 : Status) ≠ 1) h).elim
      · intro h
        exact (((incoming_vertex w i hi k).mp (hits_range h)).elim h₀ h₁).elim

def PrefixHit (w : OrientedChain G n) (c : Fin n → Choice) (i : Fin n) (k : Vertex) : Prop :=
  ∃ j : Fin n, j.val ≤ i.val ∧ Hits w c j (w.hex i k)

theorem olderHit_prior (w : OrientedChain G n) (c : Fin n → Choice) (i : Fin n) (k : Vertex) :
    (∃ j : Fin n, j.val < i.val ∧ Hits w c j (w.hex i k)) ↔ prior (incoming w c i) k = 1 := by
  by_cases hi : i.val=0
  · rw [incoming_initial w c i hi]
    constructor
    · rintro ⟨j,hj,_⟩
      omega
    · intro h
      exact ((by decide : (0 : Status) ≠ 1) h).elim
  · let j : Fin n := ⟨i.val-1,by have := i.isLt; omega⟩
    have hji : j.val+1=i.val := by change i.val-1+1=i.val; omega
    have hjn : j.val+1<n := hji ▸ i.isLt
    have eqi : i = ⟨j.val+1,hjn⟩ := Fin.ext hji.symm
    have hs := prior_one_next w c j hjn k
    rw [← eqi] at hs
    rw [hs]
    constructor
    · rintro ⟨a,ha,hh⟩
      have hclose := hit_faces_close (show w.hex i k ∈ Set.range (w.hex i) from ⟨k,rfl⟩) hh
      have he : a = j := Fin.ext (by omega)
      exact he ▸ hh
    · intro hh
      exact ⟨j,by omega,hh⟩

theorem prefixHit_matched (w : OrientedChain G n) (c : Fin n → Choice) (i : Fin n) (k : Vertex) :
    PrefixHit w c i k ↔ matched (incoming w c i) (c i) k = true := by
  rw [matched, Bool.or_eq_true, beq_iff_eq, ← hits_iff_touched, ← olderHit_prior]
  constructor
  · rintro ⟨j,hj,h⟩
    rcases lt_or_eq_of_le hj with hlt | he
    · exact Or.inr ⟨j,hlt,h⟩
    · have he' : j = i := Fin.ext he
      exact Or.inl (he' ▸ h)
  · rintro (h | ⟨j,hj,h⟩)
    · exact ⟨i,le_rfl,h⟩
    · exact ⟨j,hj.le,h⟩

theorem forgotten_covered (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (k : Vertex) (hk : port (outgoing w i) k = false) :
    Covered w c (w.hex i k) ↔ PrefixHit w c i k := by
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨j, ?_, hj⟩
    by_contra! hlt
    have hport := (port_iff_later w i k).mpr ⟨j,hlt,hits_range hj⟩
    rw [hk] at hport
    contradiction
  · rintro ⟨j,_,hj⟩
    exact ⟨j,hj⟩

#print axioms prefixHit_matched
#print axioms forgotten_covered

end Helicene
```

### `HexagonValidity.lean`

```lean
import HexagonBoundary

namespace Helicene

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

def ValidFamily (w : OrientedChain G n) (c : Fin n → Choice) : Prop :=
  ∀ i, localValid (incoming w c i) (outgoing w i) (c i)

def Unmatched (w : OrientedChain G n) (c : Fin n → Choice) (i : Fin n) (k : Vertex) : Prop :=
  matched (incoming w c i) (c i) k = false

theorem unmatched_of_uncovered (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (k : Vertex) (h : ¬ Covered w c (w.hex i k)) : Unmatched w c i k := by
  unfold Unmatched
  apply Bool.eq_false_iff.mpr
  intro hm
  obtain ⟨j,_,hj⟩ := (prefixHit_matched w c i k).mpr hm
  exact h ⟨j,hj⟩

theorem forgotten_uncovered (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (k : Vertex) (hp : port (outgoing w i) k = false)
    (hm : Unmatched w c i k) : ¬ Covered w c (w.hex i k) := by
  intro hh
  have he := (prefixHit_matched w c i k).mp ((forgotten_covered w c i k hp).mp hh)
  rw [Unmatched, he] at hm
  contradiction

def obligation (w : OrientedChain G n) (c : Fin n → Choice) (i : Fin n) (k : Vertex) : Prop :=
  required (incoming w c i) (outgoing w i) (c i) k = true

theorem obligation_iff (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (k : Vertex) :
    obligation w c i k ↔ Unmatched w c i k ∧
      (prior (incoming w c i) k = 2 ∨
        (port (outgoing w i) (k-1) = false ∧ Unmatched w c i (k-1)) ∨
        (port (outgoing w i) (k+1) = false ∧ Unmatched w c i (k+1))) := by
  simp [obligation, required, Unmatched, Bool.and_eq_true, Bool.or_eq_true, or_assoc]

theorem outgoing_some (w : OrientedChain G n) (i : Fin n) (h : i.val+1<n) :
    outgoing w i = some (w.turn i) := by simp [outgoing,h]

theorem incoming_obligation (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (k : Vertex) (h : prior (incoming w c i) k = 2) :
    ∃ (j : Fin n) (l : Vertex), j.val+1=i.val ∧ w.hex j l = w.hex i k ∧
      (l = (w.turn j).offset ∨ l = (w.turn j).offset+1) ∧ obligation w c j l := by
  have hi : i.val ≠ 0 := by
    intro hi
    rw [incoming_initial w c i hi] at h
    exact (by decide : (0 : Status) ≠ 2) h
  let j : Fin n := ⟨i.val-1, by have := i.isLt; omega⟩
  have he : j.val+1=i.val := by change i.val-1+1=i.val; omega
  have hj : j.val+1<n := he ▸ i.isLt
  have hji : (⟨j.val+1,hj⟩ : Fin n) = i := Fin.ext he
  by_cases h0 : k=0
  · subst k
    refine ⟨j,(w.turn j).offset+1,he,?_,Or.inr rfl,?_⟩
    · rw [← hji, (w.join j hj).1]
    · rw [← hji, prior_next_zero, outputStatus_required] at h
      simpa only [obligation, outgoing_some w j hj] using h
  · by_cases h1 : k=1
    · subst k
      refine ⟨j,(w.turn j).offset,he,?_,Or.inl rfl,?_⟩
      · rw [← hji, (w.join j hj).2]
      · rw [← hji, prior_next_one, outputStatus_required] at h
        simpa only [obligation, outgoing_some w j hj] using h
    · rw [prior_nonport _ _ h0 h1] at h
      exact ((by decide : (0 : Status) ≠ 2) h).elim

theorem no_inherited_at_outgoing (w : OrientedChain G n) (c : Fin n → Choice)
    (i : Fin n) (l : Vertex) (hl : l = (w.turn i).offset ∨ l = (w.turn i).offset+1) :
    prior (incoming w c i) l ≠ 2 := by
  have hn := offset_ne (w.turn i)
  rcases hl with rfl | rfl
  · rw [prior_nonport _ _ hn.1 hn.2.1]
    decide
  · rw [prior_nonport _ _ hn.2.2.1 hn.2.2.2]
    decide

theorem terminal_obligation_impossible (w : OrientedChain G n) (c : Fin n → Choice)
    (hdom : ∀ i k, Covered w c (w.hex i k) ∨ Covered w c (w.hex i (k+1)))
    (i : Fin n) (k : Vertex) (hr : obligation w c i k) (hp : port (outgoing w i) k = false) :
    False := by
  obtain ⟨hm,ho⟩ := (obligation_iff w c i k).mp hr
  have hk := forgotten_uncovered w c i k hp hm
  have neighbor (j : Fin n) (l : Vertex) (he : w.hex j l = w.hex i k)
      (h : (port (outgoing w j) (l-1) = false ∧ Unmatched w c j (l-1)) ∨
        (port (outgoing w j) (l+1) = false ∧ Unmatched w c j (l+1))) : False := by
    have hl : ¬ Covered w c (w.hex j l) := he ▸ hk
    rcases h with ⟨hp',hm'⟩ | ⟨hp',hm'⟩
    · have hh := hdom j (l-1)
      rw [vertex_sub_add] at hh
      exact hh.elim (forgotten_uncovered w c j (l-1) hp' hm') hl
    · exact (hdom j l).elim hl (forgotten_uncovered w c j (l+1) hp' hm')
  rcases ho with hprev | hcurr
  · obtain ⟨j,l,_,he,hl,hr'⟩ := incoming_obligation w c i k hprev
    rcases (obligation_iff w c j l).mp hr' with ⟨_,hprev' | hnext'⟩
    · exact no_inherited_at_outgoing w c j l hl hprev'
    · exact neighbor j l he hnext'
  · exact neighbor i k rfl hcurr

theorem satisfied_obligation (w : OrientedChain G n) (c : Fin n → Choice)
    (h : ValidFamily w c) (i : Fin n) (k : Vertex) (hr : obligation w c i k) :
    Covered w c (w.hex i k) := by
  have hp := (h i).2.2.2 k hr
  have hi : i.val+1<n := by
    by_contra hn
    simp [outgoing,hn,port] at hp
  have hj (b : Vertex) (hb : b=0 ∨ b=1)
      (hprior : prior (incoming w c ⟨i.val+1,hi⟩) b = 2)
      (he : w.hex ⟨i.val+1,hi⟩ b = w.hex i k) : Covered w c (w.hex i k) := by
    by_contra hn
    have hm := unmatched_of_uncovered w c ⟨i.val+1,hi⟩ b (he ▸ hn)
    have hr' := (obligation_iff w c ⟨i.val+1,hi⟩ b).mpr ⟨hm,Or.inl hprior⟩
    have hp' := (h ⟨i.val+1,hi⟩).2.2.2 b hr'
    rw [incoming_forgotten w i hi b hb] at hp'
    contradiction
  rw [outgoing_some w i hi, port_some] at hp
  have hr' : required (incoming w c i) (some (w.turn i)) (c i) k = true := by
    simpa only [obligation, outgoing_some w i hi] using hr
  rcases hp with rfl | rfl
  · apply hj 1 (Or.inr rfl) _ (w.join i hi).2
    rwa [prior_next_one, outputStatus_required]
  · apply hj 0 (Or.inl rfl) _ (w.join i hi).1
    rwa [prior_next_zero, outputStatus_required]

theorem valid_dominates (w : OrientedChain G n) (c : Fin n → Choice)
    (h : ValidFamily w c) (i : Fin n) (k : Vertex) :
    Covered w c (w.hex i k) ∨ Covered w c (w.hex i (k+1)) := by
  have forget (j : Fin n) (l : Vertex)
      (hf : port (outgoing w j) l = false ∨ port (outgoing w j) (l+1) = false) :
      Covered w c (w.hex j l) ∨ Covered w c (w.hex j (l+1)) := by
    by_contra! hnc
    have hm₁ := unmatched_of_uncovered w c j l hnc.1
    have hm₂ := unmatched_of_uncovered w c j (l+1) hnc.2
    rcases hf with hf | hf
    · have hr : obligation w c j (l+1) := by
        apply (obligation_iff w c j (l+1)).mpr
        exact ⟨hm₂, Or.inr (Or.inl (by simpa only [vertex_add_sub] using And.intro hf hm₁))⟩
      exact hnc.2 (satisfied_obligation w c h j (l+1) hr)
    · have hr := (obligation_iff w c j l).mpr ⟨hm₁, Or.inr (Or.inr ⟨hf,hm₂⟩)⟩
      exact hnc.1 (satisfied_obligation w c h j l hr)
  cases h₁ : port (outgoing w i) k
  · exact forget i k (Or.inl h₁)
  cases h₂ : port (outgoing w i) (k+1)
  · exact forget i k (Or.inr h₂)
  have hi : i.val+1<n := by
    by_contra hn
    simp [outgoing,hn,port] at h₁
  rw [outgoing_some w i hi, port_some] at h₁ h₂
  have hk : k = (w.turn i).offset := by
    refine h₁.elim id (fun he => ?_)
    rcases h₂ with h₂ | h₂
    · have hh : ∀ p : Vertex, p+1+1 ≠ p := by intro p; fin_cases p <;> decide
      exact (hh _ (by rwa [he] at h₂)).elim
    · exact (succ_ne ((w.turn i).offset+1) (by rw [he] at h₂; exact h₂.symm)).elim
  subst k
  have hcov := forget (⟨i.val+1,hi⟩ : Fin n) 0
    (Or.inl (incoming_forgotten w i hi 0 (Or.inl rfl)))
  change Covered w c (w.hex ⟨i.val+1,hi⟩ 0) ∨
    Covered w c (w.hex ⟨i.val+1,hi⟩ 1) at hcov
  rw [(w.join i hi).1, (w.join i hi).2] at hcov
  exact hcov.symm

theorem valid_noRepeated (w : OrientedChain G n) (c : Fin n → Choice)
    (h : ValidFamily w c) : NoRepeatedEdges c :=
  fun i hi => (h i).1 (incoming_some w c i hi)

theorem validity_iff_maximal (w : OrientedChain G n) (c : Fin n → Choice) :
    ValidFamily w c ↔ NoRepeatedEdges c ∧ IsMaximalMatching G (chosenEdges w c).val := by
  constructor
  · intro h
    have hc := valid_noRepeated w c h
    refine ⟨hc,(maximal_iff_local w c hc).mpr ⟨fun i => (h i).2.1,?_, valid_dominates w c h⟩⟩
    rintro i j hij v ⟨hi,hj⟩
    have hnext : i.val+1<n := hij ▸ j.isLt
    have he : j = ⟨i.val+1,hnext⟩ := Fin.ext hij.symm
    subst j
    obtain ⟨k,rfl⟩ := hits_range hj
    exact (h _).2.2.1 k ((hits_iff_touched w c _ k).mp hj)
      ((prior_one_next w c i hnext k).mpr hi)
  · rintro ⟨hc,hm⟩ i
    obtain ⟨hl,hcross,hdom⟩ := (maximal_iff_local w c hc).mp hm
    refine ⟨?_,hl i,?_,?_⟩
    · intro h
      apply hc i
      intro hi
      rw [incoming_initial w c i hi] at h
      contradiction
    · intro k hk hp
      obtain ⟨j,hj,hjv⟩ := (olderHit_prior w c i k).mpr hp
      have hclose := hit_faces_close (show w.hex i k ∈ Set.range (w.hex i) from ⟨k,rfl⟩) hjv
      exact hcross j i (by omega) _ ⟨hjv,(hits_iff_touched w c i k).mpr hk⟩
    · intro k hr
      cases hp : port (outgoing w i) k
      · exact (terminal_obligation_impossible w c hdom i k hr hp).elim
      · rfl

#print axioms validity_iff_maximal

end Helicene
```

### `HexagonPaths.lean`

```lean
import HexagonCertificate
import Mathlib.Data.List.Nodup

open Matrix BigOperators

namespace Helicene

def accepted : Option State → List Turn → List (List Choice)
  | a, [] => (choices.filter fun c => decide (localValid a none c)).map fun c => [c]
  | a, t :: ts => (choices.filter fun c => decide (localValid a (some t) c)).flatMap fun c =>
      (accepted (some (outputState a t c)) ts).map (c :: ·)

theorem choices_nodup : choices.Nodup := by decide +kernel

theorem mem_choices (c : Choice) : c ∈ choices := by
  have aux (a b d e f g : Bool) : (![a,b,d,e,f,g] : Choice) ∈ choices := by
    cases a <;> cases b <;> cases d <;> cases e <;> cases f <;> cases g <;> decide
  have he : (![c 0,c 1,c 2,c 3,c 4,c 5] : Choice) = c := by
    funext i
    fin_cases i <;> rfl
  rw [← he]
  exact aux .. 

theorem mem_accepted_last (a : Option State) (cs : List Choice) :
    cs ∈ accepted a [] ↔ ∃ c, cs = [c] ∧ localValid a none c := by
  simp only [accepted, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨c,⟨_,hc⟩,rfl⟩
    exact ⟨c,rfl,hc⟩
  · rintro ⟨c,rfl,hc⟩
    exact ⟨c,⟨mem_choices c,hc⟩,rfl⟩

theorem mem_accepted_cons (a : Option State) (t : Turn) (ts : List Turn)
    (cs : List Choice) :
    cs ∈ accepted a (t::ts) ↔ ∃ c ds, cs = c::ds ∧ localValid a (some t) c ∧
      ds ∈ accepted (some (outputState a t c)) ts := by
  simp only [accepted, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨c,⟨_,hc⟩,ds,hds,rfl⟩
    exact ⟨c,ds,rfl,hc,hds⟩
  · rintro ⟨c,ds,rfl,hc,hds⟩
    exact ⟨c,⟨mem_choices c,hc⟩,ds,hds,rfl⟩

theorem accepted_nodup (a : Option State) (ts : List Turn) : (accepted a ts).Nodup := by
  induction ts generalizing a with
  | nil =>
    rw [accepted]
    exact (choices_nodup.filter _).map (fun _ _ h => (List.cons.inj h).1)
  | cons t ts ih =>
    rw [accepted, List.nodup_flatMap]
    refine ⟨?_,?_⟩
    · intro c _
      exact (ih _).map (fun _ _ h => (List.cons.inj h).2)
    · apply (choices_nodup.filter _).imp
      intro c d hne
      apply List.disjoint_left.mpr
      intro cs hc hd
      obtain ⟨xs,_,he⟩ := List.mem_map.mp hc
      obtain ⟨ys,_,he'⟩ := List.mem_map.mp hd
      exact hne (List.cons.inj (he.trans he'.symm)).1

theorem accepted_length_of_mem {a : Option State} {ts : List Turn} {cs : List Choice}
    (h : cs ∈ accepted a ts) : cs.length = ts.length+1 := by
  induction ts generalizing a cs with
  | nil =>
    obtain ⟨c,rfl,_⟩ := (mem_accepted_last a cs).mp h
    rfl
  | cons t ts ih =>
    obtain ⟨c,ds,rfl,_,hd⟩ := (mem_accepted_cons a t ts cs).mp h
    simp [ih hd]

theorem group_by_state (a : Option State) (t : Turn) (cs : List Choice) (x : Row) :
    ((cs.filter fun c => decide (localValid a (some t) c)).map
        (fun c => x (outputState a t c))).sum =
      ∑ j : State, ((cs.countP fun c => decide (localValid a (some t) c) &&
        outputState a t c == j : ℕ) : ℤ) * x j := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    by_cases h : localValid a (some t) c
    · simp [h, ih, List.countP_cons, Nat.cast_add, apply_ite, add_mul, ite_mul, add_comm]
      let f : State → ℤ := fun j =>
        ((cs.countP fun c => decide (localValid a (some t) c) &&
          outputState a t c == j : ℕ) : ℤ) * x j
      let g : State → ℤ := fun j => if outputState a t c = j then x j else 0
      have hgf : (∑ j, (g j + f j)) = x (outputState a t c) + (∑ j, f j) := by
        rw [Finset.sum_add_distrib]
        simp [g]
      rw [← hgf]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h' : outputState a t c = j <;> simp [f, g, h']
    · simp [h, ih]

theorem cast_sum_lengths (f : Choice → ℕ) (cs : List Choice) :
    ((cs.map f).sum : ℤ) = (cs.map fun c => (f c : ℤ)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Nat.cast_add, ih]

theorem accepted_length_cons (a : Option State) (t : Turn) (ts : List Turn) :
    ((accepted a (t::ts)).length : ℤ) =
      ∑ j : State, transferCount a (some t) j * ((accepted (some j) ts).length : ℤ) := by
  rw [accepted, List.length_flatMap]
  simp only [List.length_map, cast_sum_lengths]
  exact group_by_state a t choices (fun j => (accepted (some j) ts).length)

theorem accepted_last (a : Option State) :
    ((accepted a []).length : ℤ) = transferCount a none 0 := by
  simp [accepted, transferCount, List.countP_eq_length_filter]

theorem mat_transfer (t : Turn) (i j : State) :
    mat t i j = transferCount (some i) (some t) j := by
  cases t
  · exact transfer_tables.2.2.1 i j
  · exact transfer_tables.2.2.2.1 i j
  · exact transfer_tables.2.2.2.2 i j

theorem accepted_suffix (ts : List Turn) (i : State) :
    ((accepted (some i) ts).length : ℤ) = (word ts *ᵥ finish) i := by
  induction ts generalizing i with
  | nil =>
    rw [accepted_last, word, one_mulVec]
    exact (transfer_tables.2.1 i).symm
  | cons t ts ih =>
    rw [accepted_length_cons, word, ← mulVec_mulVec]
    simp only [ih, mulVec, dotProduct, mat_transfer]

theorem accepted_score (ts : List Turn) :
    ((accepted none (.left :: ts)).length : ℤ) = score ts := by
  rw [accepted_length_cons]
  simp only [← transfer_tables.1, accepted_suffix, score, dotProduct]

theorem accepted_single : (accepted none []).length = 5 := by
  exact_mod_cast (accepted_last none).trans single_transfer

#print axioms accepted_score
#print axioms accepted_single

end Helicene
```

### `HexagonScan.lean`

```lean
import HexagonPaths
import HexagonValidity
import Mathlib.Data.List.OfFn

namespace Helicene

def scanState (a : Option State) (ts : List Turn) (cs : List Choice) : ℕ → Option State
  | 0 => a
  | i+1 => match ts, cs with
    | t::ts, c::cs => scanState (some (outputState a t c)) ts cs i
    | _, _ => none

theorem scanState_next (a : Option State) (ts : List Turn) (cs : List Choice) (i : ℕ)
    (ht : i < ts.length) (hc : i < cs.length) :
    scanState a ts cs (i+1) = some (outputState (scanState a ts cs i) ts[i] cs[i]) := by
  induction i generalizing a ts cs with
  | zero =>
    cases ts with
    | nil => simp at ht
    | cons t ts =>
      cases cs with
      | nil => simp at hc
      | cons c cs => simp [scanState]
  | succ i ih =>
    cases ts with
    | nil => simp at ht
    | cons t ts =>
      cases cs with
      | nil => simp at hc
      | cons c cs => exact ih _ ts cs (by simpa using ht) (by simpa using hc)

theorem mem_accepted_iff_scan (a : Option State) (ts : List Turn) (cs : List Choice) :
    cs ∈ accepted a ts ↔
      cs.length = ts.length + 1 ∧
        ∀ (i : ℕ) (hi : i < cs.length),
          localValid (scanState a ts cs i) ts[i]? cs[i] := by
  induction ts generalizing a cs with
  | nil =>
    rw [mem_accepted_last]
    constructor
    · rintro ⟨c,rfl,hc⟩
      refine ⟨rfl,fun i hi => ?_⟩
      have hh : i = 0 := by simpa using hi
      subst i
      exact hc
    · rintro ⟨hlen,hv⟩
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
        have hnil : cs = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa using hlen
        subst cs
        exact ⟨c,rfl,hv 0 (by simp)⟩
  | cons t ts ih =>
    cases cs with
    | nil =>
      rw [mem_accepted_cons]
      simp
    | cons c cs =>
      have he :
          c::cs ∈ accepted a (t::ts) ↔ localValid a (some t) c ∧
            cs ∈ accepted (some (outputState a t c)) ts := by
        rw [mem_accepted_cons]
        constructor
        · rintro ⟨d,ds,h,hd,hs⟩
          obtain ⟨rfl,rfl⟩ := List.cons.inj h
          exact ⟨hd,hs⟩
        · rintro ⟨hc,hs⟩
          exact ⟨c,cs,rfl,hc,hs⟩
      rw [he, ih]
      constructor
      · rintro ⟨hc,hlen,hv⟩
        refine ⟨by simp [hlen], fun i hi => ?_⟩
        cases i with
        | zero => exact hc
        | succ i => exact hv i (by simpa using hi)
      · rintro ⟨hlen,hv⟩
        refine ⟨hv 0 (by simp),by simpa using hlen,fun i hi => ?_⟩
        exact hv (i+1) (by simpa using hi)

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

def turnList (w : OrientedChain G n) : List Turn :=
  List.ofFn (fun i : Fin (n-1) => w.turn ⟨i.val,by have := i.isLt; omega⟩)

@[simp] theorem turnList_length (w : OrientedChain G n) : (turnList w).length = n-1 := by
  simp [turnList]

theorem turnList_get (w : OrientedChain G n) (i : Fin n)
    (h : i.val < (turnList w).length) : (turnList w)[i.val] = w.turn i := by
  simp [turnList]

theorem turnList_getOpt (w : OrientedChain G n) (i : Fin n) :
    (turnList w)[i.val]? = outgoing w i := by
  by_cases hi : i.val+1<n
  · have h : i.val < (turnList w).length := by rw [turnList_length]; omega
    rw [List.getElem?_eq_getElem h, turnList_get w i h, outgoing_some w i hi]
  · have hf : (turnList w).length ≤ i.val := by rw [turnList_length]; omega
    rw [List.getElem?_eq_none hf]
    simp [outgoing,hi]

theorem incoming_scan (w : OrientedChain G n) (c : Fin n → Choice) (i : ℕ) (hi : i<n) :
    scanState none (turnList w) (List.ofFn c) i = incoming w c ⟨i,hi⟩ := by
  induction i with
  | zero => simp [scanState,incoming_initial w c ⟨0,hi⟩ rfl]
  | succ i ih =>
    have hi' : i<n := by omega
    have ht : i < (turnList w).length := by rw [turnList_length]; omega
    have hc : i < (List.ofFn c).length := by simpa
    rw [scanState_next _ _ _ _ ht hc,ih hi',incoming_next w c ⟨i,hi'⟩ hi]
    rw [turnList_get w ⟨i,hi'⟩ ht]
    simp

theorem mem_accepted_iff_valid (w : OrientedChain G n) (hn : 0<n) (c : Fin n → Choice) :
    List.ofFn c ∈ accepted none (turnList w) ↔ ValidFamily w c := by
  rw [mem_accepted_iff_scan]
  have he : (List.ofFn c).length = (turnList w).length + 1 := by
    rw [List.length_ofFn,turnList_length]
    omega
  constructor
  · rintro ⟨_,h⟩ i
    have hi : i.val < (List.ofFn c).length := by simp
    specialize h i.val hi
    rw [incoming_scan w c i.val i.isLt, turnList_getOpt w i] at h
    simpa using h
  · intro h
    refine ⟨he, fun i hi => ?_⟩
    have hi' : i<n := by simpa using hi
    rw [incoming_scan w c i hi', turnList_getOpt w ⟨i,hi'⟩]
    simpa using h ⟨i,hi'⟩

#print axioms mem_accepted_iff_valid

end Helicene
```

### `HeliceneMinimum.lean`

```lean
import HexagonScan
import HexagonOrientation
import HexagonMinimum

namespace Helicene

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

abbrev MaximalMatchings (G : SimpleGraph V) :=
  {M : Finset (Sym2 V) // IsMaximalMatching G M}

noncomputable def validMatchings (w : OrientedChain G n) :
    {c : Fin n → Choice // ValidFamily w c} ≃ MaximalMatchings G :=
  Equiv.ofBijective
    (fun c => ⟨(chosenEdges w c.val).val, ((validity_iff_maximal w c.val).mp c.property).2⟩)
    (by
      constructor
      · intro c d h
        have hc := valid_noRepeated w c.val c.property
        have hd := valid_noRepeated w d.val d.property
        have he : (matchingChoices w).symm ⟨c.val,hc⟩ =
            (matchingChoices w).symm ⟨d.val,hd⟩ := by
          apply Subtype.ext
          exact congrArg (fun x : MaximalMatchings G => x.val) h
        have h' := (matchingChoices w).symm.injective he
        exact Subtype.ext (congrArg (fun x : {c : Fin n → Choice // NoRepeatedEdges c} => x.val) h')
      · intro M
        let E : GraphEdgeSubsets G := ⟨M.val,M.property.1.1⟩
        let c := matchingChoices w E
        have he : chosenEdges w c.val = E := (matchingChoices w).symm_apply_apply E
        have hv : ValidFamily w c.val := by
          apply (validity_iff_maximal w c.val).mpr
          refine ⟨c.property, ?_⟩
          rw [he]
          exact M.property
        exact ⟨⟨c.val,hv⟩,Subtype.ext (congrArg (fun x : GraphEdgeSubsets G => x.val) he)⟩)

noncomputable def acceptedFinset (w : OrientedChain G n) : Finset (List Choice) := by
  classical
  exact (accepted none (turnList w)).toFinset

theorem mem_acceptedFinset (w : OrientedChain G n) (cs : List Choice) :
    cs ∈ acceptedFinset w ↔ cs ∈ accepted none (turnList w) := by
  classical
  simp [acceptedFinset]

noncomputable def validPaths (w : OrientedChain G n) (hn : 0<n) :
    {c : Fin n → Choice // ValidFamily w c} ≃ acceptedFinset w :=
  Equiv.ofBijective
    (fun c => ⟨List.ofFn c.val, (mem_acceptedFinset w _).2
      ((mem_accepted_iff_valid w hn c.val).2 c.property)⟩)
    (by
      constructor
      · intro c d h
        exact Subtype.ext (List.ofFn_injective (congrArg Subtype.val h))
      · intro cs
        have hmem := (mem_acceptedFinset w cs.val).mp cs.property
        have hlen : cs.val.length = n := by
          have hl := accepted_length_of_mem hmem
          rw [turnList_length] at hl
          omega
        let c : Fin n → Choice := fun i => cs.val[i.val]'(by rw [hlen]; exact i.isLt)
        have hc : List.ofFn c = cs.val := by
          apply List.ext_getElem
          · simp [hlen]
          · intros
            simp [c]
        have hv : ValidFamily w c := (mem_accepted_iff_valid w hn c).mp (hc ▸ hmem)
        exact ⟨⟨c,hv⟩,Subtype.ext hc⟩)

noncomputable def matchingPaths (w : OrientedChain G n) (hn : 0<n) :
    MaximalMatchings G ≃ acceptedFinset w :=
  (validMatchings w).symm.trans (validPaths w hn)

theorem psi_eq_paths [Fintype V] (w : OrientedChain G n) (hn : 0<n) :
    Ψ G = (accepted none (turnList w)).length := by
  classical
  rw [Ψ, ← Fintype.card_subtype]
  rw [Fintype.card_congr (matchingPaths w hn),Fintype.card_coe]
  exact List.toFinset_card_of_nodup (accepted_nodup none (turnList w))

theorem psi_zero [Fintype V] (w : BenzenoidChainWitness G 0) : Ψ G = 1 := by
  classical
  have noVertex (v : V) : False := by
    obtain ⟨i,_,_⟩ := w.verts_cover v
    exact Fin.elim0 i
  have noEdge (e : Sym2 V) : False := by
    induction e using Sym2.ind with
    | h a b => exact noVertex a
  rw [Ψ]
  apply Finset.card_eq_one.mpr
  refine ⟨∅, ?_⟩
  ext M
  have empty : M = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun e => (noEdge e).elim)
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,empty]
  exact ⟨fun _ => True.intro, fun _ => ⟨⟨fun e => (noEdge e).elim,fun e => (noEdge e).elim⟩,
    fun e => (noEdge e).elim⟩⟩

theorem psi_one [Fintype V] (w : OrientedChain G 1) : Ψ G = 5 := by
  rw [psi_eq_paths w (by decide)]
  have he : turnList w = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [turnList_length]
  rw [he, accepted_single]

theorem turnList_helicene (n : ℕ) :
    turnList (orientedHelicene n) = List.replicate (n-1) .left := by
  rw [turnList]
  exact List.ofFn_const _ _

theorem turnList_head (w : OrientedChain G n) (hn : 2≤n) :
    ∃ ts : List Turn, turnList w = .left::ts := by
  have hp : 0 < (turnList w).length := by rw [turnList_length]; omega
  let i : Fin n := ⟨0,by omega⟩
  have hfirst := turnList_get w i hp
  change (turnList w)[0] = w.turn i at hfirst
  rw [w.first i rfl] at hfirst
  revert hp hfirst
  rcases turnList w with _ | ⟨t,ts⟩
  · simp
  · intro hp hfirst
    exact ⟨ts,by simpa using hfirst⟩

theorem MathDB331692 {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (w : BenzenoidChainWitness G n) : Ψ (helicene n) ≤ Ψ G := by
  rcases n with _ | n
  · rw [psi_zero w, psi_zero (heliceneWitness 0)]
  rcases n with _ | n
  · rw [psi_one (orient w), psi_one (orientedHelicene 1)]
  have hn : 0 < n+1+1 := by omega
  have ht : 2 ≤ n+1+1 := by omega
  obtain ⟨ts,he⟩ := turnList_head (orient w) ht
  have hl : ts.length = n := by
    have he' := congrArg List.length he
    simp only [turnList_length, List.length_cons] at he'
    omega
  rw [psi_eq_paths (orient w) hn, psi_eq_paths (orientedHelicene _) hn, he, turnList_helicene]
  rw [show n+1+1-1 = n+1 by omega, List.replicate_succ]
  have hm := transfer_minimum ts
  rw [hl, ← accepted_score, ← accepted_score] at hm
  exact_mod_cast hm

#check MathDB331692
#print axioms MathDB331692
#print axioms matchingPaths
#print axioms psi_eq_paths

end Helicene
```

