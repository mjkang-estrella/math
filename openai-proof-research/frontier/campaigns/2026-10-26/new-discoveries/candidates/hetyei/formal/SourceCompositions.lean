import GridKernel

open Finset
namespace FlatBernoulli
noncomputable section

/-- Split off the first block of an ordered composition. -/
def prependComposition (n : ℕ) (p : (j : Fin (n+1)) × Composition (n-j)) :
    Composition (n+1) where
  blocks := (p.1.val+1)::p.2.blocks
  blocks_pos := by
    intro i hi
    rcases List.mem_cons.mp hi with h | h
    · omega
    · exact p.2.blocks_pos h
  blocks_sum := by
    simp only [List.sum_cons,Composition.blocks_sum]
    have := p.1.isLt
    omega

theorem prependComposition_injective (n : ℕ) : Function.Injective (prependComposition n) := by
  rintro ⟨j,c⟩ ⟨k,d⟩ he
  have hb := congrArg Composition.blocks he
  change (j.val+1)::c.blocks = (k.val+1)::d.blocks at hb
  have hjk : j=k := Fin.ext (by have := List.cons.inj hb; omega)
  subst k
  have hcd : c=d := Composition.ext (List.cons.inj hb).2
  subst d
  rfl

theorem prependComposition_surjective (n : ℕ) : Function.Surjective (prependComposition n) := by
  rintro ⟨l,hpos,hsum⟩
  cases l with
  | nil => simp at hsum
  | cons a l =>
    have ha : 0 < a := hpos (by simp)
    have hsum' : a+l.sum=n+1 := hsum
    have htail : ∀ i, i ∈ l → 0 < i := fun i hi => hpos (List.mem_cons_of_mem a hi)
    let j : Fin (n+1) := ⟨a-1,by omega⟩
    let c : Composition (n-j) := ⟨l,(fun {i} hi => htail i hi),by dsimp [j];omega⟩
    refine ⟨⟨j,c⟩,?_⟩
    apply Composition.ext
    change (a-1+1)::l = a::l
    rw [Nat.sub_add_cancel (by omega)]

def prependCompositionEquiv (n : ℕ) :
    ((j : Fin (n+1)) × Composition (n-j)) ≃ Composition (n+1) :=
  Equiv.ofBijective (prependComposition n)
    ⟨prependComposition_injective n,prependComposition_surjective n⟩

/-- Singleton blocks have weight zero, so summing all positive compositions
is literally the same finite sum as restricting every block to at least two. -/
def blockWeight (b : ℕ) : ℝ := if 2 ≤ b then 1/((b:ℝ)*(b-1:ℕ)) else 0

def normalizedComposition (n : ℕ) : ℝ :=
  ∑ c : Composition n, (c.blocks.map blockWeight).prod

theorem normalizedComposition_zero : normalizedComposition 0 = 1 := by
  have he : ∀ c : Composition 0, (c.blocks.map blockWeight).prod = 1 := by
    intro c
    rw [(Composition.blocks_eq_nil c).mpr rfl]
    rfl
  simp [normalizedComposition,he,composition_card]

theorem normalizedComposition_succ (n : ℕ) :
    normalizedComposition (n+1) = ∑ j : Fin (n+1),
      blockWeight (j.val+1)*normalizedComposition (n-j) := by
  unfold normalizedComposition
  rw [← (prependCompositionEquiv n).sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ c : Composition (n-j),
    ((prependComposition n ⟨j,c⟩).blocks.map blockWeight).prod) = _
  simp only [prependComposition,List.map_cons,List.prod_cons]
  rw [Finset.mul_sum]

theorem normalizedComposition_one : normalizedComposition 1 = 0 := by
  rw [show 1=0+1 by rfl,normalizedComposition_succ]
  simp [blockWeight]

theorem normalizedComposition_recurrence (n : ℕ) :
    normalizedComposition (n+2) = ∑ k ∈ Finset.range (n+1),
      (1/(((k:ℝ)+2)*((k:ℝ)+1)))*normalizedComposition (n-k) := by
  rw [show n+2=(n+1)+1 by omega,normalizedComposition_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,zero_add,blockWeight,show ¬2 ≤ 1 by omega,ite_false,zero_mul,
    zero_add,Fin.val_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k =>
    (if 2 ≤ k+1+1 then 1/(((k+1+1:ℕ):ℝ)*((k+1+1-1:ℕ):ℝ)) else 0)*
      normalizedComposition (n+1-(k+1))) (n+1)]
  apply Finset.sum_congr rfl
  intro k _
  simp only [show 2 ≤ k+1+1 by omega,ite_true,Nat.add_sub_cancel,
    Nat.cast_add,Nat.cast_one,show n+1-(k+1)=n-k by omega]
  congr 2
  ring

theorem normalizedComposition_eq_renewal (n : ℕ) :
    normalizedComposition n = renewalCoefficient n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | (_ | n)
    · simpa only [renewalCoefficient] using normalizedComposition_zero
    · simpa only [Nat.zero_add,renewalCoefficient] using normalizedComposition_one
    · rw [normalizedComposition_recurrence,renewalCoefficient]
      apply Finset.sum_congr rfl
      intro k _
      rw [ih (n-k) (by omega)]

end
end FlatBernoulli
