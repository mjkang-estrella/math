import Antimagic4ADepthTwo
namespace Antimagic.Round4A

/-- The displacement permutation used by the higher-depth leaf construction. -/
theorem sigma_range (k a : ℕ) (ha : 1 ≤ a ∧ a ≤ 2 * k) :
    1 ≤ sigma k a ∧ sigma k a ≤ 2 * k := by
  unfold sigma
  split_ifs <;> omega

theorem sigma_injective (k : ℕ) {a b : ℕ}
    (ha : 1 ≤ a ∧ a ≤ 2 * k) (hb : 1 ≤ b ∧ b ≤ 2 * k)
    (he : sigma k a = sigma k b) : a = b := by
  unfold sigma at he
  split_ifs at he <;> omega

/-- Zero-based destination block of a slot in the published tuple order. -/
def leafBlock (s j : ℕ) : ℕ :=
  if j < 2 * s - 2 then if j % 2 = 0 then j / 2 else 2 * s - 1 - j / 2
  else if j = 2 * s - 2 then s - 1 else s

def leafResidue (s k a j : ℕ) : ℕ :=
  if j < 2 * s - 2 then if j % 2 = 0 then a else 2 * k + 1 - a
  else if j = 2 * s - 2 then a else 2 * k + 1 - sigma k a

def leafEntry (s k a j : ℕ) : ℕ := leafBlock s j * (2 * k) + leafResidue s k a j

theorem leafBlock_range (s j : ℕ) (hs : 1 ≤ s) (hj : j < 2 * s) : leafBlock s j < 2 * s := by
  unfold leafBlock
  split_ifs <;> omega

theorem leafBlock_injective (s : ℕ) (hs : 1 ≤ s) :
    Function.Injective (fun j : Fin (2 * s) => leafBlock s j.val) := by
  intro j l he
  have hj := j.isLt
  have hl := l.isLt
  dsimp only at he
  apply Fin.ext
  unfold leafBlock at he
  split_ifs at he <;> omega

theorem leafResidue_range (s k a j : ℕ) (ha : 1 ≤ a ∧ a ≤ 2 * k) :
    1 ≤ leafResidue s k a j ∧ leafResidue s k a j ≤ 2 * k := by
  have := sigma_range k a ha
  unfold leafResidue
  split_ifs <;> omega

theorem leafResidue_injective (s k j : ℕ) {a b : ℕ}
    (ha : 1 ≤ a ∧ a ≤ 2 * k) (hb : 1 ≤ b ∧ b ≤ 2 * k)
    (he : leafResidue s k a j = leafResidue s k b j) : a = b := by
  have hsa := sigma_range k a ha
  have hsb := sigma_range k b hb
  unfold leafResidue at he
  split_ifs at he
  · exact he
  · omega
  · exact he
  · exact sigma_injective k ha hb (by omega)

theorem leafEntry_range (s k a j : ℕ) (hs : 1 ≤ s)
    (ha : 1 ≤ a ∧ a ≤ 2 * k) (hj : j < 2 * s) :
    1 ≤ leafEntry s k a j ∧ leafEntry s k a j ≤ (2 * s) * (2 * k) := by
  have hb := leafBlock_range s j hs hj
  have hr := leafResidue_range s k a j ha
  have hm := Nat.mul_le_mul_right (2 * k) (show leafBlock s j + 1 ≤ 2 * s by omega)
  unfold leafEntry
  constructor
  · omega
  · nlinarith

theorem leafEntry_injective (s k : ℕ) (hs : 1 ≤ s) :
    Function.Injective (fun p : Fin (2 * k) × Fin (2 * s) => leafEntry s k (p.1.val + 1) p.2.val) := by
  rintro ⟨a,j⟩ ⟨b,l⟩ he
  change leafEntry s k (a.val + 1) j.val = leafEntry s k (b.val + 1) l.val at he
  have ha : 1 ≤ a.val + 1 ∧ a.val + 1 ≤ 2 * k := by have := a.isLt; omega
  have hb : 1 ≤ b.val + 1 ∧ b.val + 1 ≤ 2 * k := by have := b.isLt; omega
  have hc := block_unique (2 * k) _ _ _ _ (leafResidue_range s k _ _ ha)
    (leafResidue_range s k _ _ hb) he
  have hjl : j = l := leafBlock_injective s hs hc.1
  subst l
  have hab := leafResidue_injective s k j.val ha hb hc.2
  change a.val + 1 = b.val + 1 at hab
  exact Prod.ext (Fin.ext (Nat.add_right_cancel hab)) rfl

def leafMap (s k : ℕ) (hs : 1 ≤ s) (p : Fin (2 * k) × Fin (2 * s)) :
    Fin ((2 * s) * (2 * k)) :=
  ⟨leafEntry s k (p.1.val + 1) p.2.val - 1, by
    have := leafEntry_range s k (p.1.val + 1) p.2.val hs (by have := p.1.isLt; omega) p.2.isLt
    omega⟩

theorem leafMap_bijective (s k : ℕ) (hs : 1 ≤ s) : Function.Bijective (leafMap s k hs) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro p q he
    apply leafEntry_injective s k hs
    change leafEntry s k (p.1.val + 1) p.2.val = leafEntry s k (q.1.val + 1) q.2.val
    have hp := leafEntry_range s k (p.1.val + 1) p.2.val hs (by have := p.1.isLt; omega) p.2.isLt
    have hq := leafEntry_range s k (q.1.val + 1) q.2.val hs (by have := q.1.isLt; omega) q.2.isLt
    have h := congrArg Fin.val he
    change leafEntry s k (p.1.val + 1) p.2.val - 1 = leafEntry s k (q.1.val + 1) q.2.val - 1 at h
    omega
  · simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

/-- This is precisely the leaf part of the frozen `largeLabel`, whenever
its parent-label-derived tuple parameter is a. -/
theorem largeLabel_leaf (s n i a : ℕ) (hs : 1 ≤ s) (_hn : 3 ≤ n)
    (ha : (if center (2 * s) n < internalLabel (2 * s) n (n - 1) (i / (2 * s))
      then internalLabel (2 * s) n (n - 1) (i / (2 * s)) - center (2 * s) n
      else (2 * s) ^ (n - 1) + 1 + internalLabel (2 * s) n (n - 1) (i / (2 * s)) - center (2 * s) n) = a)
    (hk : (2 * s) ^ (n - 1) = 2 * ((2 * s) ^ (n - 1) / 2)) :
    largeLabel (2 * s) n n i = internalEdges (2 * s) n +
      leafEntry s ((2 * s) ^ (n - 1) / 2) a (i % (2 * s)) := by
  have hj : i % (2 * s) < 2 * s := Nat.mod_lt _ (by omega)
  simp only [largeLabel, lt_self_iff_false, ite_false, ha,
    Nat.mul_div_cancel_left s (by decide : 0 < 2)]
  unfold leafEntry leafBlock leafResidue
  simp only [← hk]
  split_ifs <;>
    have hsub : 2 * s + 1 - (i % (2 * s) / 2 + 1) - 1 = 2 * s - 1 - i % (2 * s) / 2 := by omega
  all_goals try simp only [Nat.add_sub_cancel]
  all_goals try rw [hsub]
  all_goals omega


/-- Every outer leaf pair has a constant sum. -/
theorem leafEntry_outer_pair (s k a b : ℕ) (hs : 1 ≤ s)
    (ha : 1 ≤ a ∧ a ≤ 2 * k) (hb : b < s - 1) :
    leafEntry s k a (2 * b) + leafEntry s k a (2 * b + 1) = (2 * s) * (2 * k) + 1 := by
  simp only [leafEntry, leafBlock, leafResidue,
    show 2 * b < 2 * s - 2 by omega, show 2 * b + 1 < 2 * s - 2 by omega,
    show 2 * b % 2 = 0 by omega, show (2 * b + 1) % 2 ≠ 0 by omega,
    show 2 * b / 2 = b by omega, show (2 * b + 1) / 2 = b by omega, ite_true, ite_false]
  have h1 : 2 * s - 1 - b + b + 1 = 2 * s := by omega
  have h2 : 2 * k + 1 - a + a = 2 * k + 1 := by omega
  nlinarith

theorem leafEntry_middle_pair (s k a : ℕ) (hs : 1 ≤ s)
    (ha : 1 ≤ a ∧ a ≤ 2 * k) :
    leafEntry s k a (2 * s - 2) + leafEntry s k a (2 * s - 1) + sigma k a =
      (2 * s) * (2 * k) + 1 + a := by
  have hr := sigma_range k a ha
  simp only [leafEntry, leafBlock, leafResidue, lt_self_iff_false, ite_false,
    ite_true, show ¬ (2 * s - 1 < 2 * s - 2) by omega,
    show ¬ (2 * s - 1 = 2 * s - 2) by omega]
  have h1 : s - 1 + 1 = s := by omega
  have h2 : 2 * k + 1 - sigma k a + sigma k a = 2 * k + 1 := by omega
  nlinarith

open Finset in
/-- Exact displacement identity for each full leaf tuple. Natural subtraction
is avoided on the right: the permutation is added back to the left. -/
theorem leafEntry_sum (s k a : ℕ) (hs : 1 ≤ s) (ha : 1 ≤ a ∧ a ≤ 2 * k) :
    (∑ j ∈ range (2 * s), leafEntry s k a j) + sigma k a =
      s * ((2 * s) * (2 * k) + 1) + a := by
  have he : 2 * s = (2 * (s - 1) + 1) + 1 := by omega
  nth_rw 1 [he]
  rw [sum_range_succ, sum_range_succ, Round3.sum_range_pairs]
  have hout : (∑ b ∈ range (s - 1), (leafEntry s k a (2 * b) + leafEntry s k a (2 * b + 1))) =
      (s - 1) * ((2 * s) * (2 * k) + 1) := by
    calc
      _ = ∑ _b ∈ range (s - 1), ((2 * s) * (2 * k) + 1) := by
        apply sum_congr rfl
        intro b hb
        exact leafEntry_outer_pair s k a b hs ha (mem_range.mp hb)
      _ = _ := by simp
  rw [hout, show 2 * (s - 1) = 2 * s - 2 by omega,
    show 2 * s - 2 + 1 = 2 * s - 1 by omega]
  have hmid := leafEntry_middle_pair s k a hs ha
  have hprod := congrArg (fun x => x * ((2 * s) * (2 * k) + 1))
    (show s - 1 + 1 = s by omega)
  nlinarith

#print axioms leafMap_bijective
#print axioms largeLabel_leaf
#print axioms leafEntry_sum
end Antimagic.Round4A
