/-
Gate E semantic controls, written by the independent reviewer. Facts are derived from the
source definitions `Arc`/`Reach`/`Token`/`Out` by direct closure arguments, not from the authors'
reachability bridge. Only `Bun.card_out`, `Bun.card_token` and the endpoint are used, for the
counts of the token universe and to confirm the endpoint's instance at these vertices.
-/
import BunFinalModel

namespace ControlE

theorem lt01 : ((0:Fin 2):Nat) < ((1:Fin 2):Nat) := by decide

def hF : Token 2 := htok 0 1 lt01 false
def hT : Token 2 := htok 0 1 lt01 true
def v0 : Token 2 := vtok 0
def v1 : Token 2 := vtok 1

theorem fin2_cases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
theorem fin2_key : ∀ x y : Fin 2, (x:Nat) < (y:Nat) → x = 0 ∧ y = 1 := by decide

theorem htok_eq (i j : Fin 2) (h : (i:Nat) < (j:Nat)) (l : Bool) :
    htok i j h l = htok 0 1 lt01 l := by
  obtain ⟨rfl, rfl⟩ := fin2_key i j h
  rfl

/-- The exact set reachable from `(0,false)` in the n=2 bunkbed, in terms of the four tokens. -/
def Q (ω : Out 2) (i : Nat) (l : Bool) : Prop :=
  (i = 0 ∧ l = false) ∨
  (i = 0 ∧ l = true ∧ ω v0 = true) ∨
  (i = 1 ∧ l = false ∧ (ω hF = true ∨ (ω v0 = true ∧ ω hT = true ∧ ω v1 = true))) ∨
  (i = 1 ∧ l = true ∧ ((ω v0 = true ∧ ω hT = true) ∨ (ω hF = true ∧ ω v1 = true)))

theorem Q_step {ω : Out 2} {y1 : Fin 2} {y2 : Bool} {z1 : Fin 2} {z2 : Bool}
    (hy : Q ω y1.val y2) (h : Arc 2 ω (y1, y2) (z1, z2)) : Q ω z1.val z2 := by
  rcases arc_cases h with ⟨hl, hlt, hw⟩ | ⟨he, hne, hw⟩
  · have hl' : y2 = z2 := hl
    have hlt' : (y1:Nat) < (z1:Nat) := hlt
    have hw' : ω (htok 0 1 lt01 y2) = true := by
      rw [← htok_eq y1 z1 hlt' y2]; exact hw
    subst hl'
    obtain ⟨rfl, rfl⟩ := fin2_key y1 z1 hlt'
    cases y2 with
    | false => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inl hw'⟩))
    | true =>
      rcases hy with ⟨_, h1⟩ | ⟨_, _, hc⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd h1 (by decide)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, Or.inl ⟨hc, hw'⟩⟩))
      · exact absurd h1 (by decide)
      · exact absurd h1 (by decide)
  · have he' : y1 = z1 := he
    have hne' : y2 ≠ z2 := hne
    have hw' : ω (vtok y1) = true := hw
    subst he'
    rcases fin2_cases y1 with rfl | rfl
    · cases y2 <;> cases z2
      · exact absurd rfl hne'
      · exact Or.inr (Or.inl ⟨rfl, rfl, hw'⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd rfl hne'
    · cases y2 <;> cases z2
      · exact absurd rfl hne'
      · rcases hy with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, hx⟩ | ⟨_, h1, _⟩
        · exact absurd h1 (by decide)
        · exact absurd h1 (by decide)
        · rcases hx with ha | ⟨hc, hb, _⟩
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, Or.inr ⟨ha, hw'⟩⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, Or.inl ⟨hc, hb⟩⟩))
        · exact absurd h1 (by decide)
      · rcases hy with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩ | ⟨_, _, hx⟩
        · exact absurd h1 (by decide)
        · exact absurd h1 (by decide)
        · exact absurd h1 (by decide)
        · rcases hx with ⟨hc, hb⟩ | ⟨ha, _⟩
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inr ⟨hc, hb, hw'⟩⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inl ha⟩))
      · exact absurd rfl hne'

theorem reach_Q {ω : Out 2} {y : Vert 2} (h : Reach 2 ω ((0:Fin 2), false) y) :
    Q ω y.1.val y.2 := by
  induction h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | @tail b c _ h2 ih =>
    obtain ⟨b1, b2⟩ := b
    obtain ⟨c1, c2⟩ := c
    exact Q_step ih h2

theorem reach_true_iff (ω : Out 2) :
    Reach 2 ω ((0:Fin 2), false) ((1:Fin 2), true) ↔
      ((ω v0 = true ∧ ω hT = true) ∨ (ω hF = true ∧ ω v1 = true)) := by
  constructor
  · intro h
    rcases reach_Q h with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, h1, _⟩ | ⟨_, _, hx⟩
    · exact absurd h0 (by decide)
    · exact absurd h0 (by decide)
    · exact absurd h1 (by decide)
    · exact hx
  · rintro (⟨hc, hb⟩ | ⟨ha, hd⟩)
    · exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single
          (show Arc 2 ω ((0:Fin 2), false) ((0:Fin 2), true) from Or.inr ⟨rfl, by decide, hc⟩))
        (show Arc 2 ω ((0:Fin 2), true) ((1:Fin 2), true) from Or.inl ⟨rfl, ⟨lt01, hb⟩⟩)
    · exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single
          (show Arc 2 ω ((0:Fin 2), false) ((1:Fin 2), false) from Or.inl ⟨rfl, ⟨lt01, ha⟩⟩))
        (show Arc 2 ω ((1:Fin 2), false) ((1:Fin 2), true) from Or.inr ⟨rfl, by decide, hd⟩)

theorem reach_false_iff (ω : Out 2) :
    Reach 2 ω ((0:Fin 2), false) ((1:Fin 2), false) ↔
      (ω hF = true ∨ (ω v0 = true ∧ ω hT = true ∧ ω v1 = true)) := by
  constructor
  · intro h
    rcases reach_Q h with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, _, hx⟩ | ⟨_, h1, _⟩
    · exact absurd h0 (by decide)
    · exact absurd h0 (by decide)
    · exact hx
    · exact absurd h1 (by decide)
  · rintro (ha | ⟨hc, hb, hd⟩)
    · exact Relation.ReflTransGen.single
        (show Arc 2 ω ((0:Fin 2), false) ((1:Fin 2), false) from Or.inl ⟨rfl, ⟨lt01, ha⟩⟩)
    · exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.single
            (show Arc 2 ω ((0:Fin 2), false) ((0:Fin 2), true) from Or.inr ⟨rfl, by decide, hc⟩))
          (show Arc 2 ω ((0:Fin 2), true) ((1:Fin 2), true) from Or.inl ⟨rfl, ⟨lt01, hb⟩⟩))
        (show Arc 2 ω ((1:Fin 2), true) ((1:Fin 2), false) from Or.inr ⟨rfl, by decide, hd⟩)

/-- The Boolean cube on exactly the four tokens of the n=2 model. -/
def enc (ω : Out 2) : Bool × Bool × Bool × Bool := (ω hF, ω hT, ω v0, ω v1)

def dec : Bool × Bool × Bool × Bool → Token 2 → Bool
  | p, Sum.inl h => if h.layer then p.2.1 else p.1
  | p, Sum.inr k => if k.val = 0 then p.2.2.1 else p.2.2.2

def eqv : Out 2 ≃ Bool × Bool × Bool × Bool where
  toFun := enc
  invFun p := dec p
  left_inv ω := by
    funext t
    rcases t with ⟨i, j, hlt, l⟩ | k
    · obtain ⟨rfl, rfl⟩ := fin2_key i j hlt
      cases l <;> rfl
    · rcases fin2_cases k with rfl | rfl <;> rfl
  right_inv p := by
    obtain ⟨a, b, c, d⟩ := p
    rfl

def gT (p : Bool × Bool × Bool × Bool) : Bool := (p.2.2.1 && p.2.1) || (p.1 && p.2.2.2)
def gF (p : Bool × Bool × Bool × Bool) : Bool := p.1 || (p.2.2.1 && p.2.1 && p.2.2.2)

theorem gT_count : Fintype.card {p : Bool × Bool × Bool × Bool // gT p = true} = 7 := by decide
theorem gF_count : Fintype.card {p : Bool × Bool × Bool × Bool // gF p = true} = 9 := by decide

theorem gT_iff (ω : Out 2) :
    ((ω v0 = true ∧ ω hT = true) ∨ (ω hF = true ∧ ω v1 = true)) ↔ gT (eqv ω) = true := by
  show _ ↔ ((ω v0 && ω hT) || (ω hF && ω v1)) = true
  simp

theorem gF_iff (ω : Out 2) :
    (ω hF = true ∨ (ω v0 = true ∧ ω hT = true ∧ ω v1 = true)) ↔ gF (eqv ω) = true := by
  show _ ↔ (ω hF || (ω v0 && ω hT && ω v1)) = true
  simp [and_assoc]

open Classical in
/-- Exact hand-derived count: 7 of 16 outcomes reach `(1,true)` from `(0,false)`. -/
theorem count_n2_true :
    Fintype.card {ω : Out 2 // Reach 2 ω ((0:Fin 2), false) ((1:Fin 2), true)} = 7 :=
  (Fintype.card_congr (eqv.subtypeEquiv
    (fun ω => (reach_true_iff ω).trans (gT_iff ω)))).trans gT_count

open Classical in
/-- Exact hand-derived count: 9 of 16 outcomes reach `(1,false)` from `(0,false)`. -/
theorem count_n2_false :
    Fintype.card {ω : Out 2 // Reach 2 ω ((0:Fin 2), false) ((1:Fin 2), false)} = 9 :=
  (Fintype.card_congr (eqv.subtypeEquiv
    (fun ω => (reach_false_iff ω).trans (gF_iff ω)))).trans gF_count

open Classical in
/-- Direction control: the inequality reversed is FALSE at n=2, u=0, v=1. -/
theorem swapped_false_n2 :
    ¬ (Fintype.card {ω : Out 2 // Reach 2 ω ((0:Fin 2), false) ((1:Fin 2), false)} ≤
       Fintype.card {ω : Out 2 // Reach 2 ω ((0:Fin 2), false) ((1:Fin 2), true)}) := by
  rw [count_n2_false, count_n2_true]
  decide

open Classical in
/-- The endpoint at these vertices agrees with the hand counts, `7 ≤ 9`. -/
theorem endpoint_instance : (7:Nat) ≤ 9 := by
  have h := Bun.bunkbed_E7_transitive 2 (0:Fin 2) (1:Fin 2)
  rw [count_n2_true, count_n2_false] at h
  exact h

/-! ### n = 1, u = v = 0 -/

theorem token1 (t : Token 1) : t = Sum.inr (0 : Fin 1) := by
  rcases t with ⟨i, j, hlt, l⟩ | k
  · exfalso
    have hi := i.isLt
    have hj := j.isLt
    omega
  · exact congrArg Sum.inr (Subsingleton.elim k 0)

/-- Single-vertex reachability of the opposite layer holds exactly through the post token,
derived directly from `Arc`. -/
theorem reach_n1_true_iff (ω : Out 1) :
    Reach 1 ω ((0:Fin 1), false) ((0:Fin 1), true) ↔ ω (vtok 0) = true := by
  constructor
  · intro h
    have key : ∀ b : Vert 1, Reach 1 ω ((0:Fin 1), false) b → b.2 = true → ω (vtok 0) = true := by
      intro b hb
      induction hb with
      | refl => intro h1; exact absurd h1 (by decide)
      | @tail b c _ h2 ih =>
        intro hc
        obtain ⟨b1, b2⟩ := b
        obtain ⟨c1, c2⟩ := c
        rcases arc_cases h2 with ⟨hl, hlt, _⟩ | ⟨_, _, hw⟩
        · exfalso
          have h1 : b1.val < c1.val := hlt
          have hi := b1.isLt
          have hj := c1.isLt
          omega
        · have hb0 : b1 = 0 := Subsingleton.elim _ _
          rw [hb0] at hw
          exact hw
    exact key _ h rfl
  · intro h
    exact Relation.ReflTransGen.single
      (show Arc 1 ω ((0:Fin 1), false) ((0:Fin 1), true) from Or.inr ⟨rfl, by decide, h⟩)

open Classical in
theorem count_n1_true :
    Fintype.card {ω : Out 1 // Reach 1 ω ((0:Fin 1), false) ((0:Fin 1), true)} = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨fun _ => true, (reach_n1_true_iff _).mpr rfl⟩, ?_⟩
  rintro ⟨y, hy⟩
  apply Subtype.ext
  funext t
  have hv : y (vtok 0) = true := (reach_n1_true_iff y).mp hy
  rw [token1 t]
  exact hv

theorem card_out_one : Fintype.card (Out 1) = 2 := by
  simpa using Bun.card_out 1

open Classical in
theorem count_n1_false :
    Fintype.card {ω : Out 1 // Reach 1 ω ((0:Fin 1), false) ((0:Fin 1), false)} = 2 := by
  have h : Fintype.card {ω : Out 1 // Reach 1 ω ((0:Fin 1), false) ((0:Fin 1), false)}
      = Fintype.card (Out 1) :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ => Relation.ReflTransGen.refl))
  rw [h, card_out_one]

open Classical in
/-- Direction control at n=1. -/
theorem swapped_false_n1 :
    ¬ (Fintype.card {ω : Out 1 // Reach 1 ω ((0:Fin 1), false) ((0:Fin 1), false)} ≤
       Fintype.card {ω : Out 1 // Reach 1 ω ((0:Fin 1), false) ((0:Fin 1), true)}) := by
  rw [count_n1_false, count_n1_true]
  decide

/-! ### Shared vertical token, layer separation, no reverse arcs, token universe -/

theorem arc_vert_iff (n : Nat) (ω : Out n) (i : Fin n) (l : Bool) :
    Arc n ω (i, l) (i, !l) ↔ ω (vtok i) = true := by
  constructor
  · intro h
    rcases arc_cases h with ⟨hl, _⟩ | ⟨_, _, hw⟩
    · exact absurd hl (by cases l <;> simp)
    · exact hw
  · intro h
    exact arc_vert h

/-- The two directions of a vertical edge are controlled by the same single token. -/
theorem vertical_shared (n : Nat) (ω : Out n) (i : Fin n) :
    Arc n ω (i, false) (i, true) ↔ Arc n ω (i, true) (i, false) := by
  have h1 := arc_vert_iff n ω i false
  have h2 := arc_vert_iff n ω i true
  simp only [Bool.not_false, Bool.not_true] at h1 h2
  exact h1.trans h2.symm

def layerOf : Token 2 → Bool
  | Sum.inl a => a.layer
  | Sum.inr _ => false

/-- The two layers' horizontal tokens for the same arc are distinct. -/
theorem layers_distinct : hF ≠ hT := by
  intro h
  have h2 : (false : Bool) = true := congrArg layerOf h
  cases h2

/-- There is no horizontal arc against the transitive order. -/
theorem no_reverse_arc (ω : Out 2) (l : Bool) : ¬ Arc 2 ω ((1:Fin 2), l) ((0:Fin 2), l) := by
  intro h
  rcases arc_cases h with ⟨_, hlt, _⟩ | ⟨he, _, _⟩
  · have hlt' : ((1:Fin 2):Nat) < ((0:Fin 2):Nat) := hlt
    exact absurd hlt' (by decide)
  · have he' : (1:Fin 2) = 0 := he
    exact absurd he' (by decide)

open Classical in
/-- `v < u` gives an empty event: 0 outcomes. -/
theorem reverse_count_zero :
    Fintype.card {ω : Out 2 // Reach 2 ω ((1:Fin 2), false) ((0:Fin 2), false)} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun x => absurd (reach_fst_le x.2) (by decide)⟩

/-- Token universe: one vertical token per index, two horizontal per transitive arc. -/
theorem card_token_one : Fintype.card (Token 1) = 1 := by
  simpa using Bun.card_token 1

theorem card_token_two : Fintype.card (Token 2) = 4 := by
  simpa using Bun.card_token 2

theorem card_out_two : Fintype.card (Out 2) = 16 := by
  rw [Bun.card_out]
  decide

/-- `n = 0`: no vertices exist, the endpoint is vacuous. -/
theorem n0_vacuous (u : Fin 0) : False := u.elim0

end ControlE

#print axioms ControlE.count_n2_true
#print axioms ControlE.count_n2_false
#print axioms ControlE.swapped_false_n2
#print axioms ControlE.endpoint_instance
#print axioms ControlE.count_n1_true
#print axioms ControlE.count_n1_false
#print axioms ControlE.swapped_false_n1
#print axioms ControlE.vertical_shared
#print axioms ControlE.reverse_count_zero
