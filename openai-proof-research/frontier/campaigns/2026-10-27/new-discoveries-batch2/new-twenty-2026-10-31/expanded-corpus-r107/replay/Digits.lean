import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
namespace Digits356756

def Digit (k t : ℤ) : Prop := (0 ≤ t ∧ t ≤ 2*k) ∨ t = 2*k+2

def energy (k t : ℤ) : ℤ := 4*t^2 - (12*k-2)*(if t % 2 = 0 then 1 else -1)

lemma triple_classify (k a b c : ℤ) (hk : 3 ≤ k)
    (ha : Digit k a) (hb : Digit k b) (hc : Digit k c)
    (h : (4*k+1) ∣ a-2*b+c) :
    a-2*b+c = 0 ∨
    (a = 2*k+2 ∧ b = 0 ∧ c = 2*k-1) ∨
    (a = 2*k-1 ∧ b = 0 ∧ c = 2*k+2) ∨
    (b = 2*k+2 ∧ a+c = 3) := by
  obtain ⟨u, hu⟩ := h
  have ha' : 0 ≤ a ∧ a ≤ 2*k+2 := by unfold Digit at ha; omega
  have hb' : 0 ≤ b ∧ b ≤ 2*k+2 := by unfold Digit at hb; omega
  have hc' : 0 ≤ c ∧ c ≤ 2*k+2 := by unfold Digit at hc; omega
  have ulo : -1 ≤ u := by
    by_contra hh
    have huu : u ≤ -2 := by omega
    nlinarith
  have uhi : u ≤ 1 := by
    by_contra hh
    have huu : 2 ≤ u := by omega
    nlinarith
  have cases : u = -1 ∨ u = 0 ∨ u = 1 := by omega
  unfold Digit at ha hb hc
  rcases cases with rfl | rfl | rfl <;> simp only [mul_neg, mul_one, mul_zero] at hu <;> omega

lemma local_classify (k a b c d : ℤ) (hk : 3 ≤ k)
    (ha : Digit k a) (hb : Digit k b) (hc : Digit k c) (hd : Digit k d)
    (h1 : (4*k+1) ∣ a-2*b+c) (h2 : (4*k+1) ∣ b-2*c+d) :
    (a-2*b+c = 0 ∧ b-2*c+d = 0) ∨
    (a = 2*k-1 ∧ b = 0 ∧ c = 2*k+2 ∧ d = 3) ∨
    (a = 3 ∧ b = 2*k+2 ∧ c = 0 ∧ d = 2*k-1) := by
  have t1 := triple_classify k a b c hk ha hb hc h1
  have t2 := triple_classify k b c d hk hb hc hd h2
  unfold Digit at ha hb hc hd
  omega

lemma ordinary_gap (k a b c d : ℤ)
    (h1 : a-2*b+c = 0) (h2 : b-2*c+d = 0) :
    energy k a + energy k d - energy k b - energy k c = 16*(b-a)^2 := by
  have hb : b = a+(b-a) := by omega
  have hc : c = a+2*(b-a) := by omega
  have hd : d = a+3*(b-a) := by omega
  unfold energy
  have pa : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have pb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases pa with pa | pa <;> rcases pb with pb | pb
  all_goals
    have pc : c % 2 = a % 2 := by omega
    have pd : d % 2 = b % 2 := by omega
    simp only [pc, pd, pa, pb]
    norm_num
    rw [hc, hd]
    ring

lemma gap_nonneg (k a b c d : ℤ) (hk : 3 ≤ k)
    (ha : Digit k a) (hb : Digit k b) (hc : Digit k c) (hd : Digit k d)
    (h1 : (4*k+1) ∣ a-2*b+c) (h2 : (4*k+1) ∣ b-2*c+d) :
    0 ≤ energy k a + energy k d - energy k b - energy k c ∧
    (energy k a + energy k d - energy k b - energy k c = 0 → a=b ∧ b=c ∧ c=d) := by
  rcases local_classify k a b c d hk ha hb hc hd h1 h2 with hn | he | he
  · rw [ordinary_gap k a b c d hn.1 hn.2]
    constructor
    · positivity
    · intro hz; have : b-a = 0 := by nlinarith [sq_nonneg (b-a)]
      omega
  · rcases he with ⟨rfl,rfl,rfl,rfl⟩
    unfold energy
    have hodd : (2*k-1)%2 = 1 := by omega
    have heven : (2*k+2)%2 = 0 := by omega
    simp only [hodd,heven]
    norm_num
    constructor
    · nlinarith
    · intro hz; nlinarith
  · rcases he with ⟨rfl,rfl,rfl,rfl⟩
    unfold energy
    have hodd : (2*k-1)%2 = 1 := by omega
    have heven : (2*k+2)%2 = 0 := by omega
    simp only [hodd,heven]
    norm_num
    constructor
    · nlinarith
    · intro hz; nlinarith


open scoped BigOperators

def SourceDigit (p : ℕ) (t : ℕ) : Prop := t ≤ (p-1)/2 ∨ t = (p+3)/2

def SourceSet (p n : ℕ) [NeZero p] (x : Fin n → ZMod p) : Prop :=
  (∀ i, SourceDigit p (x i).val) ∧
  ∀ t : ZMod p, SourceDigit p t.val →
    (Finset.univ.filter (fun i => x i = t)).card = n / ((p+3)/2)

lemma same_histogram {p n : ℕ} [NeZero p] {x y : Fin n → ZMod p}
    (hx : SourceSet p n x) (hy : SourceSet p n y) (t : ZMod p) :
    (Finset.univ.filter (fun i => x i = t)).card =
    (Finset.univ.filter (fun i => y i = t)).card := by
  classical
  by_cases ht : SourceDigit p t.val
  · rw [hx.2 t ht,hy.2 t ht]
  · have hxx : Finset.univ.filter (fun i => x i = t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hh := (Finset.mem_filter.mp hi).2
      exact ht (hh ▸ hx.1 i)
    have hyy : Finset.univ.filter (fun i => y i = t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hh := (Finset.mem_filter.mp hi).2
      exact ht (hh ▸ hy.1 i)
    rw [hxx,hyy]

lemma sum_same {p n : ℕ} [NeZero p] {x y : Fin n → ZMod p}
    (hx : SourceSet p n x) (hy : SourceSet p n y) (f : ZMod p → ℤ) :
    ∑ i, f (x i) = ∑ i, f (y i) := by
  classical
  have expand (v : Fin n → ZMod p) :
      ∑ i, f (v i) = ∑ t : ZMod p, ((Finset.univ.filter (fun i => v i = t)).card : ℤ) * f t := by
    calc
      ∑ i, f (v i) = ∑ i, ∑ t : ZMod p, if v i = t then f t else 0 := by simp
      _ = ∑ t : ZMod p, ∑ i, if v i = t then f t else 0 := Finset.sum_comm
      _ = _ := by congr 1; ext t; simp [← Finset.sum_filter]
  rw [expand x,expand y]
  congr 1
  ext t
  rw [same_histogram hx hy t]

lemma digit_bridge {p : ℕ} {k : ℤ} (hp : (p : ℤ) = 4*k+1) (hk : 3 ≤ k) {t : ℕ}
    (ht : SourceDigit p t) : Digit k (t : ℤ) := by
  unfold SourceDigit at ht
  unfold Digit
  omega

lemma dvd_bridge {p : ℕ} [NeZero p] {a b c : ZMod p}
    (h : a-2*b+c = 0) : (p : ℤ) ∣ (a.val : ℤ)-2*(b.val : ℤ)+(c.val : ℤ) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  simpa using h

/-- All four vectors must coincide; this forbids every nonconstant four-term progression. -/
theorem full_scope {p n : ℕ} [NeZero p] (hp : 13 ≤ p) (hmod : p % 4 = 1)
    {a b c d : Fin n → ZMod p}
    (ha : SourceSet p n a) (hb : SourceSet p n b)
    (hc : SourceSet p n c) (hd : SourceSet p n d)
    (h1 : ∀ i, a i - 2*b i + c i = 0)
    (h2 : ∀ i, b i - 2*c i + d i = 0) : a=b ∧ b=c ∧ c=d := by
  classical
  let k : ℤ := (p/4 : ℕ)
  have hk : 3 ≤ k := by dsimp [k]; omega
  have hpk : (p : ℤ) = 4*k+1 := by dsimp [k]; omega
  let gap (i : Fin n) : ℤ := energy k (a i).val + energy k (d i).val -
    energy k (b i).val - energy k (c i).val
  have hlocal (i : Fin n) : 0 ≤ gap i ∧ (gap i = 0 →
      (a i).val = (b i).val ∧ (b i).val = (c i).val ∧ (c i).val = (d i).val) := by
    have hh := gap_nonneg k (a i).val (b i).val (c i).val (d i).val hk
      (digit_bridge hpk hk (ha.1 i)) (digit_bridge hpk hk (hb.1 i))
      (digit_bridge hpk hk (hc.1 i)) (digit_bridge hpk hk (hd.1 i))
      (by rw [← hpk]; exact dvd_bridge (h1 i))
      (by rw [← hpk]; exact dvd_bridge (h2 i))
    exact ⟨hh.1,fun hz => by have eqs := hh.2 hz; exact_mod_cast eqs⟩
  have hab := sum_same ha hb (fun t => energy k t.val)
  have hcd := sum_same hc hd (fun t => energy k t.val)
  have total : ∑ i, gap i = 0 := by
    dsimp [gap]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
    omega
  have zeros (i : Fin n) : gap i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hlocal j).1)).mp total i (Finset.mem_univ i)
  have equalities (i : Fin n) := (hlocal i).2 (zeros i)
  constructor
  · funext i; exact ZMod.val_injective p (equalities i).1
  · constructor
    · funext i; exact ZMod.val_injective p (equalities i).2.1
    · funext i; exact ZMod.val_injective p (equalities i).2.2

/-- Literal prime-modulus conjecture; divisibility of the dimension is retained. -/
theorem mathdb_356756 {p n : ℕ} [NeZero p] (_hprime : p.Prime)
    (hp : 13 ≤ p) (hmod : p % 4 = 1) (_hn : (p+3)/2 ∣ n) :
    ¬ ∃ a b c d : Fin n → ZMod p,
      SourceSet p n a ∧ SourceSet p n b ∧ SourceSet p n c ∧ SourceSet p n d ∧
      (∀ i, a i - 2*b i + c i = 0) ∧ (∀ i, b i - 2*c i + d i = 0) ∧ a ≠ b := by
  rintro ⟨a,b,c,d,ha,hb,hc,hd,h1,h2,hab⟩
  exact hab (full_scope hp hmod ha hb hc hd h1 h2).1

theorem no_affine_progression {p n : ℕ} [NeZero p] (hprime : p.Prime)
    (hp : 13 ≤ p) (hmod : p % 4 = 1) (hn : (p+3)/2 ∣ n)
    (x r : Fin n → ZMod p) (hr : r ≠ 0)
    (hs : ∀ j : Fin 4, SourceSet p n (fun i => x i + (j.val : ZMod p)*r i)) : False := by
  apply mathdb_356756 hprime hp hmod hn
  refine ⟨x, (fun i => x i+r i), (fun i => x i+2*r i), (fun i => x i+3*r i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hs 0
  · simpa using hs 1
  · simpa using hs 2
  · simpa using hs 3
  · intro i; ring
  · intro i; ring
  · intro heq
    apply hr
    funext i
    have hi := congrFun heq i
    simpa using (add_left_cancel (show x i + r i = x i + 0 by simpa using hi.symm))

#print axioms mathdb_356756
#print axioms no_affine_progression
end Digits356756
