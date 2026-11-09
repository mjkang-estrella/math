import Mathlib

open Finset
namespace BergmanUnitCircle

def A (m n r : ℕ) (z : ℂ) : ℂ := ∑ p ∈ range m, z^(p-(n*p+r)/m)

lemma floor_le_index {m n r p : ℕ} (hmn : n < m) (hr : r < m) :
    (n*p+r)/m ≤ p := by
  have hm : 0 < m := by omega
  have hp : n*p+r < m*(p+1) := by nlinarith
  have hh : (n*p+r)/m < p+1 := (Nat.div_lt_iff_lt_mul hm).mpr (by simpa [mul_comm] using hp)
  omega

lemma carry_unique {m n p q : ℕ} (hcop : Nat.Coprime m n)
    (hp : p < m) (hq : q < m) (hdp : m ∣ n*p+1) (hdq : m ∣ n*q+1) : p=q := by
  have he : n*p+1 ≡ n*q+1 [MOD m] := by
    show (n*p+1)%m=(n*q+1)%m
    rw [Nat.mod_eq_zero_of_dvd hdp, Nat.mod_eq_zero_of_dvd hdq]
  have he' := Nat.ModEq.add_right_cancel' 1 he
  exact (Nat.ModEq.cancel_left_of_coprime hcop he').eq_of_lt_of_lt hp hq

lemma carry_exists {m n : ℕ} (hm : 1 < m) (hcop : Nat.Coprime m n) :
    ∃ p < m, m ∣ n*p+1 := by
  let f : Fin m → Fin m := fun p => ⟨(n*p.val+1)%m,Nat.mod_lt _ (by omega)⟩
  have hi : Function.Injective f := by
    intro p q he
    have he' : n*p.val+1 ≡ n*q.val+1 [MOD m] := congrArg Fin.val he
    have he'' := Nat.ModEq.add_right_cancel' 1 he'
    exact Fin.ext ((Nat.ModEq.cancel_left_of_coprime hcop he'').eq_of_lt_of_lt p.isLt q.isLt)
  obtain ⟨p,hp⟩ := Finite.surjective_of_injective hi (⟨0,by omega⟩ : Fin m)
  refine ⟨p.val,p.isLt,?_⟩
  exact Nat.dvd_of_mod_eq_zero (congrArg Fin.val hp)

lemma A_difference {m n p : ℕ} (hn : 0 < n) (hmn : n < m)
    (hcop : Nat.Coprime m n) (hp : p < m) (hd : m ∣ n*p+1) (z : ℂ) :
    A m n 1 z - A m n 0 z = z^(p-(n*p)/m-1)*(1-z) := by
  have hm : 1 < m := by omega
  have hf := floor_le_index hmn (by omega : 1 < m) (p:=p)
  have hc : (n*p+1)/m=(n*p)/m+1 := Nat.succ_div_of_dvd hd
  have hq : (n*p)/m < p := by omega
  have hs : (∑ q ∈ range m, (z^(q-(n*q+1)/m)-z^(q-(n*q)/m))) =
      z^(p-((n*p)/m+1))-z^(p-(n*p)/m) := by
    rw [Finset.sum_eq_single p]
    · rw [hc]
    · intro q hqm hqp
      have hnd : ¬ m ∣ n*q+1 := by
        intro hdq
        exact hqp (carry_unique hcop (mem_range.mp hqm) hp hdq hd)
      rw [Nat.succ_div_of_not_dvd hnd]
      simp
    · intro hnot
      exact (hnot (mem_range.mpr hp)).elim
  unfold A
  rw [← Finset.sum_sub_distrib]
  simp only [add_zero]
  rw [hs]
  have hex : p-(n*p)/m=(p-(n*p)/m-1)+1 := by omega
  have hex' : p-((n*p)/m+1)=p-(n*p)/m-1 := by omega
  have hpw : z^(p-(n*p)/m)=z^(p-(n*p)/m-1)*z := by
    calc
      z^(p-(n*p)/m)=z^((p-(n*p)/m-1)+1) := congrArg (fun e => z^e) hex
      _ = z^(p-(n*p)/m-1)*z := pow_succ _ _
  rw [hex',hpw]
  ring

lemma A_zero_at_one {m n : ℕ} : A m n 0 1 = (m:ℂ) := by simp [A]

lemma A_some_nonzero {m n : ℕ} (hn : 0 < n) (hmn : n < m)
    (hcop : Nat.Coprime m n) {z : ℂ} (hz : z≠0) :
    ∃ r < m, A m n r z≠0 := by
  by_cases he : z=1
  · refine ⟨0,by omega,?_⟩
    rw [he,A_zero_at_one]
    exact_mod_cast (by omega : m≠0)
  · obtain ⟨p,hp,hd⟩ := carry_exists (by omega : 1 < m) hcop
    have hdif := A_difference hn hmn hcop hp hd z
    by_cases ha : A m n 0 z=0
    · refine ⟨1,by omega,?_⟩
      intro hb
      rw [ha,hb] at hdif
      have hpz : z^(p-(n*p)/m-1)≠0 := pow_ne_zero _ hz
      have h1 : (1-z:ℂ)≠0 := sub_ne_zero.mpr (Ne.symm he)
      exact (mul_ne_zero hpz h1) (by simpa using hdif.symm)
    · exact ⟨0,by omega,ha⟩

noncomputable def gram (m n : ℕ) (z : ℂ) : ℝ :=
  ∑ r ∈ range m, Complex.normSq (A m n r z)

theorem gram_pos {m n : ℕ} (hn : 0 < n) (hmn : n < m)
    (hcop : Nat.Coprime m n) {z : ℂ} (hz : z ≠ 0) :
    0 < gram m n z := by
  obtain ⟨r,hr,ha⟩ := A_some_nonzero hn hmn hcop hz
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨r,mem_range.mpr hr,Complex.normSq_pos.mpr ha⟩

end BergmanUnitCircle
