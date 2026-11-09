import Antimagic7AParameters
namespace Antimagic.Round7A
open Round4A Round5A Round6A

theorem leaf_formula (n i : ℕ) (hn : 3  ≤  n) :
    largeLabel 2 n n i = internalEdges 2 n +
      leafEntry 1 (2^(n-1)/2) (parentParameter 2 n (i/2)) (i%2) := by
  exact largeLabel_leaf 1 n i _ (by decide) hn rfl (even_power 2 (n-1) (by decide) (by omega))

theorem leaf_range (n i : ℕ) (hn : 3  ≤  n) (hi : i<2^n) :
    internalEdges 2 n < largeLabel 2 n n i ∧
    largeLabel 2 n n i  ≤  internalEdges 2 n+2^n := by
  have hpow : 2^n=2^(n-1)*2 := by rw [← pow_succ,show n-1+1=n by omega]
  have hb : i/2<2^(n-1) := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr (by omega)
  have ha := parentParameter_range n (i/2) hn hb
  have hp := even_power 2 (n-1) (by decide) (by omega)
  have hr := leafEntry_range 1 (2^(n-1)/2) (parentParameter 2 n (i/2)) (i%2)
    (by decide) (by omega) (Nat.mod_lt _ (by decide))
  rw [leaf_formula n i hn]
  norm_num only at hr
  omega

theorem leaf_row_injective (n : ℕ) (hn : 3  ≤  n) :
    Function.Injective (fun i : Fin (2^n) => largeLabel 2 n n i.val) := by
  intro i j eq
  dsimp only at eq
  have hp := even_power 2 (n-1) (by decide) (by omega)
  have bound (x : Fin (2^n)) : x.val/2<2^(n-1) := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
    have hpow : 2^n=2^(n-1)*2 := by rw [← pow_succ,show n-1+1=n by omega]
    have := x.isLt; omega
  have param (x : Fin (2^n)) := parentParameter_range n (x.val/2) hn (bound x)
  rw [leaf_formula n i.val hn,leaf_formula n j.val hn] at eq
  have hij := leafEntry_injective 1 (2^(n-1)/2) (by decide)
    (a₁ := (⟨parentParameter 2 n (i.val/2)-1,by have := param i; omega⟩,⟨i.val%2,Nat.mod_lt _ (by decide)⟩))
    (a₂ := (⟨parentParameter 2 n (j.val/2)-1,by have := param j; omega⟩,⟨j.val%2,Nat.mod_lt _ (by decide)⟩))
    (by dsimp only; rw [Nat.sub_add_cancel (param i).1,Nat.sub_add_cancel (param j).1]; omega)
  have hrem := congrArg (fun p : Fin (2*(2^(n-1)/2)) × Fin 2 => p.2.val) hij
  have hpar := congrArg (fun p : Fin (2*(2^(n-1)/2)) × Fin 2 => p.1.val) hij
  have hquot := parentParameter_injective n hn (a₁ := ⟨i.val/2,bound i⟩) (a₂ := ⟨j.val/2,bound j⟩)
    (by dsimp only; have := param i; have := param j; dsimp only at hpar; omega)
  have hq := congrArg Fin.val hquot
  apply Fin.ext
  have := Nat.div_add_mod i.val 2
  have := Nat.div_add_mod j.val 2
  dsimp only at hrem hq
  omega

def leafRowMap (n : ℕ) (hn : 3  ≤  n) (i : Fin (2^n)) : Fin (2^n) :=
  ⟨largeLabel 2 n n i.val-(internalEdges 2 n+1),by have := leaf_range n i.val hn i.isLt; omega⟩

theorem leafRowMap_bijective (n : ℕ) (hn : 3  ≤  n) : Function.Bijective (leafRowMap n hn) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,rfl⟩
  intro i j eq
  apply leaf_row_injective n hn
  have h := congrArg Fin.val eq
  change largeLabel 2 n n i.val-(internalEdges 2 n+1)=largeLabel 2 n n j.val-(internalEdges 2 n+1) at h
  have := leaf_range n i.val hn i.isLt
  have := leaf_range n j.val hn j.isLt
  dsimp only
  omega
#print axioms leafRowMap_bijective
end Antimagic.Round7A
