import BunDomFiberSums
namespace BunDom
open Classical Bun Finset
noncomputable local instance (j : Nat) : DecidableEq (Fin (j+1)) := Classical.decEq _
def prefixEventEquiv {n j : Nat} (hn : j+1 < n) (p : Asg n j)
    (H : Asg n (j+1) → Prop) :
    {w : Asg n (j+1) // res n j w = p ∧ H w} ≃
      {f : Fresh j // H (join (p,f))} where
  toFun w := ⟨(split hn w.1).2, by
    have he : join (p,(split hn w.1).2) = w.1 := by
      have hp : (p,(split hn w.1).2) = split hn w.1 := Prod.ext w.2.1.symm rfl
      rw [hp, join_split hn]
    rw [he]; exact w.2.2⟩
  invFun f := ⟨join (p,f.1), res_join hn p f.1, f.2⟩
  left_inv w := by
    apply Subtype.ext
    have hp : (p,(split hn w.1).2) = split hn w.1 := Prod.ext w.2.1.symm rfl
    change join (p,(split hn w.1).2) = w.1
    rw [hp, join_split hn]
  right_inv f := by
    apply Subtype.ext
    exact congrArg Prod.snd (split_join hn (p,f.1))
theorem hor_join_hit {n j : Nat} (hn : j+1 < n) (p : Asg n j)
    (f : Fresh j) (R : Finset Nat) (l : Bool) :
    hor hn R l (join (p,f)) = hit (fun i : Fin (j+1) => i.1 ∈ R) (fun i => f.1 i l) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [hit, decide_eq_true_eq] using hor_join hn p f R l
theorem actual_increment_card {n j : Nat} (hn : j+1 < n) (p : Asg n j)
    (R S : Finset Nat) (d : Bool × Bool) :
    Fintype.card {w : Asg n (j+1) // res n j w = p ∧
      ind (hor hn R false w) (hor hn S true w) (w (fresV hn)) = d} =
      incrementWeight j (fun i : Fin (j+1) => i.1 ∈ R) (fun i : Fin (j+1) => i.1 ∈ S) d := by
  rw [Fintype.card_congr (prefixEventEquiv hn p _)]
  have e : {f : Fresh j // ind (hor hn R false (join (p,f)))
      (hor hn S true (join (p,f))) (join (p,f) (fresV hn)) = d} ≃
    {f : Fresh j // freshInd j (fun i : Fin (j+1) => i.1 ∈ R) (fun i : Fin (j+1) => i.1 ∈ S) f = d} :=
    Equiv.subtypeEquivRight (fun f => by
      rw [hor_join_hit hn, hor_join_hit hn]
      have hz : join (p,f) (fresV hn) = f.2 := by simp [join, fresV, tmax]
      rw [hz]; rfl)
  exact (Fintype.card_congr e).trans (increment_card j _ _ d)
def boundedSetEquiv (j : Nat) (R : Finset Nat) (hR : ∀ i ∈ R, i ≤ j) :
    {i : Fin (j+1) // i.1 ∈ R} ≃ {i // i ∈ R} where
  toFun i := ⟨i.1.1,i.2⟩
  invFun i := ⟨⟨i.1, by have := hR i.1 i.2; omega⟩, i.2⟩
  left_inv i := rfl
  right_inv i := rfl
theorem rowCount_set (j : Nat) (R : Finset Nat) (hR : ∀ i ∈ R, i ≤ j) (x : Bool) :
    rowCount (fun i : Fin (j+1) => i.1 ∈ R) x =
      if x then 2^(j+1) - 2^(j+1-R.card) else 2^(j+1-R.card) := by
  let : DecidablePred (fun i : Fin (j+1) => i.1 ∈ R) := fun _ => Classical.propDecidable _
  have hc : Fintype.card {i : Fin (j+1) // i.1 ∈ R} = R.card :=
    (Fintype.card_congr (boundedSetEquiv j R hR)).trans (Fintype.card_coe R)
  simp only [rowCount, Fintype.card_fin, hc]
end BunDom
