import Antimagic5AVertices
namespace Antimagic.Round5A
open Round4A

theorem leaf_row_injective (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) :
    Function.Injective (fun i : Fin ((2*s)^n) => largeLabel (2*s) n n i.val) := by
  intro i j eq
  dsimp only at eq
  have he : Even (2*s) := ⟨s,by omega⟩
  have hp := even_power (2*s) (n-1) he (by omega)
  have bound (x : Fin ((2*s)^n)) : x.val/(2*s) < (2*s)^(n-1) := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2*s)).mpr
    have hx := x.isLt
    have hexp : (2*s)^n = (2*s)^(n-1)*(2*s) := by rw [← pow_succ,show n-1+1=n by omega]
    omega
  have param (x : Fin ((2*s)^n)) := parentParameter_range (2*s) n (x.val/(2*s)) (by omega) he hn (bound x)
  have hm (x : Fin ((2*s)^n)) := Nat.mod_lt x.val (by omega : 0 < 2*s)
  have form (x : Fin ((2*s)^n)) : largeLabel (2*s) n n x.val = internalEdges (2*s) n +
      leafEntry s ((2*s)^(n-1)/2) (parentParameter (2*s) n (x.val/(2*s))) (x.val%(2*s)) := by
    conv_lhs => arg 4; rw [← Nat.div_add_mod x.val (2*s)]
    exact leaf_formula s n _ _ hs hn (hm x)
  rw [form i,form j] at eq
  have hij := leafEntry_injective s ((2*s)^(n-1)/2) (by omega)
    (a₁ := (⟨parentParameter (2*s) n (i.val/(2*s))-1,by have := param i; omega⟩,⟨i.val%(2*s),hm i⟩))
    (a₂ := (⟨parentParameter (2*s) n (j.val/(2*s))-1,by have := param j; omega⟩,⟨j.val%(2*s),hm j⟩))
    (by
      dsimp only
      rw [Nat.sub_add_cancel (param i).1,Nat.sub_add_cancel (param j).1]
      omega)
  have hrem := congrArg (fun p : Fin (2*((2*s)^(n-1)/2)) × Fin (2*s) => p.2.val) hij
  have hpar := congrArg (fun p : Fin (2*((2*s)^(n-1)/2)) × Fin (2*s) => p.1.val) hij
  have hquot := parentParameter_injective (2*s) n (by omega) he hn
    (a₁ := ⟨i.val/(2*s),bound i⟩) (a₂ := ⟨j.val/(2*s),bound j⟩) (by
      dsimp only
      have hi := param i
      have hj := param j
      dsimp only at hpar
      omega)
  have hq := congrArg (fun a : Fin ((2*s)^(n-1)) => a.val) hquot
  have hi := Nat.div_add_mod i.val (2*s)
  have hj := Nat.div_add_mod j.val (2*s)
  apply Fin.ext
  dsimp only at hrem hq
  rw [hq] at hi
  omega

def leafRowMap (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) (i : Fin ((2*s)^n)) : Fin ((2*s)^n) :=
  ⟨largeLabel (2*s) n n i.val - (internalEdges (2*s) n + 1),by
    have he : Even (2*s) := ⟨s,by omega⟩
    have hb := formula_range_rows s n n i.val hs hn (by omega) (by omega) i.isLt
    have hq : i.val/(2*s) < (2*s)^(n-1) := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2*s)).mpr
      have hexp : (2*s)^n = (2*s)^(n-1)*(2*s) := by rw [← pow_succ,show n-1+1=n by omega]
      have := i.isLt; omega
    have ha := parentParameter_range (2*s) n _ (by omega) he hn hq
    have hp := even_power (2*s) (n-1) he (by omega)
    have hr := leafEntry_range s ((2*s)^(n-1)/2) (parentParameter (2*s) n (i.val/(2*s)))
      (i.val%(2*s)) (by omega) (by omega) (Nat.mod_lt _ (by omega))
    have hf := leaf_formula s n (i.val/(2*s)) (i.val%(2*s)) hs hn (Nat.mod_lt _ (by omega))
    rw [Nat.div_add_mod] at hf
    simp only [label,show n ≠ 1 by omega,show n ≠ 2 by omega,ite_false] at hb
    omega⟩

theorem leafRowMap_bijective (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) :
    Function.Bijective (leafRowMap s n hs hn) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,rfl⟩
  intro i j eq
  apply leaf_row_injective s n hs hn
  dsimp only
  have h := congrArg Fin.val eq
  change largeLabel (2*s) n n i.val - (internalEdges (2*s) n+1) =
    largeLabel (2*s) n n j.val - (internalEdges (2*s) n+1) at h
  have hi := (leafRowMap s n hs hn i).isLt
  have hj := (leafRowMap s n hs hn j).isLt
  -- Positivity above the internal band follows directly from the tuple formula.
  have above (x : Fin ((2*s)^n)) : internalEdges (2*s) n < largeLabel (2*s) n n x.val := by
    have he : Even (2*s) := ⟨s,by omega⟩
    have hq : x.val/(2*s) < (2*s)^(n-1) := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2*s)).mpr
      have hexp : (2*s)^n = (2*s)^(n-1)*(2*s) := by rw [← pow_succ,show n-1+1=n by omega]
      have := x.isLt; omega
    have ha := parentParameter_range (2*s) n _ (by omega) he hn hq
    have hp := even_power (2*s) (n-1) he (by omega)
    have hr := leafEntry_range s ((2*s)^(n-1)/2) (parentParameter (2*s) n (x.val/(2*s)))
      (x.val%(2*s)) (by omega) (by omega) (Nat.mod_lt _ (by omega))
    have hf := leaf_formula s n (x.val/(2*s)) (x.val%(2*s)) hs hn (Nat.mod_lt _ (by omega))
    rw [Nat.div_add_mod] at hf
    omega
  have := above i
  have := above j
  omega

#print axioms leafRowMap_bijective
end Antimagic.Round5A
