import Std
namespace Percolation.CNF
set_option autoImplicit false

-- A pair (variable, bit) is the literal saying the variable differs from bit.
-- Thus bit=true denotes a negative literal.
abbrev Clause (α : Type) := List (α × Bool)
def Holds {α : Type} (v : α → Bool) (c : Clause α) : Prop :=
  ∃ z ∈ c, v z.1 ≠ z.2

def bits (n : Nat) : List (List Bool) :=
  Nat.rec [[]] (fun _ prev => prev.flatMap (fun xs => [false :: xs, true :: xs])) n

theorem bits_length (n : Nat) : ∀ bs ∈ bits n, bs.length = n := by
  induction n with
  | zero => intro bs hb; change bs ∈ [[]] at hb; simpa using hb
  | succ n ih =>
    intro bs hb
    change bs ∈ (bits n).flatMap (fun xs => [false :: xs, true :: xs]) at hb
    obtain ⟨xs, hx, hb⟩ := List.mem_flatMap.mp hb
    have hl := ih xs hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp [hl]

def gate {α : Type} (support : List α) (test : List Bool → Bool) : List (Clause α) :=
  ((bits support.length).filter (fun bs => !(test bs))).map (fun bs => support.zip bs)

theorem zip_agree {α : Type} (v : α → Bool) (support : List α) (bs : List Bool)
    (hl : support.length = bs.length)
    (hn : ¬ Holds v (support.zip bs)) : support.map v = bs := by
  induction support generalizing bs with
  | nil => cases bs <;> simp_all
  | cons x xs ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      have hx : v x = b := by
        apply Classical.byContradiction
        intro h
        exact hn ⟨(x,b), by simp, h⟩
      have ht : ¬ Holds v (xs.zip bs) := by
        rintro ⟨z, hz, he⟩
        exact hn ⟨z, by simp [hz], he⟩
      have he := ih bs (by simpa using hl) ht
      simp [hx, he]

theorem gate_sound {α : Type} (v : α → Bool) (support : List α)
    (test : List Bool → Bool) (ht : test (support.map v) = true) :
    ∀ c ∈ gate support test, Holds v c := by
  intro c hc
  obtain ⟨bs, hb, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hb, hf⟩ := List.mem_filter.mp hb
  apply Classical.byContradiction
  intro hn
  have he := zip_agree v support bs (bits_length _ bs hb).symm hn
  rw [← he, ht] at hf
  contradiction
end Percolation.CNF
