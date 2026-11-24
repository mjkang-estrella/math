# Complete Lean source appendix

Modules are listed in import order. Each block is byte-identical to src/.

### `HilbertDefinitions.lean`

```lean
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option linter.unusedSimpArgs false
noncomputable section
open scoped ENNReal
namespace HilbertCode
attribute [local instance] Classical.propDecidable
abbrev E := lp (fun _ : ℕ+ => ℝ) 2
local instance : DecidableEq E := Classical.decEq _
def α : ℝ := Real.sqrt 2 * Real.pi / 3
def c : ℝ := 1 - α / 2
def q : ℝ := α ^ 2 - α
def T : ℝ := Real.pi ^ 2 / 6 - 1
def w (k : ℕ+) : ℝ := 1 / (k : ℝ)
def H : Set E := {x | ∀ k : ℕ+, 0 ≤ x k ∧ x k ≤ w k}
def e (k : ℕ+) : E := lp.single 2 k 1

lemma alpha_sq : α ^ 2 = 2 * Real.pi ^ 2 / 9 := by
  unfold α
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
lemma alpha_bounds : 1 < α ∧ α < 2 := by
  have hp := Real.pi_gt_three
  have hp' := Real.pi_lt_four
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hs' := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hlow : 1 < Real.sqrt 2 := by nlinarith
  have hhigh : Real.sqrt 2 < 3/2 := by nlinarith
  unfold α
  constructor
  · nlinarith
  · nlinarith
lemma constants : 0 < c ∧ c < 1/2 ∧ 0 < q ∧ q < α ∧
    T + c^2 = q ∧ 4*T +
      (c^2 + (1-c)^2 + 2*(2*c-1)^2 + (c-1)^2 + c^2) = 6*q := by
  obtain ⟨hl, hu⟩ := alpha_bounds
  have hs := alpha_sq
  dsimp [c, q, T]
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma w_pos (k : ℕ+) : 0 < w k := by
  unfold w
  positivity
lemma hasSum_weights : HasSum (fun k : ℕ+ => w k ^ 2) (Real.pi ^ 2 / 6) := by
  have hz := hasSum_zeta_two
  have hp := (hasSum_pnat_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)^2)).2 (by simpa using hz)
  simpa [w, div_pow] using hp

lemma memlp_of_bounds (f : ℕ+ → ℝ) (hf : ∀ k, 0 ≤ f k ∧ f k ≤ w k) :
    Memℓp f 2 := by
  apply memℓp_gen
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _ hasSum_weights.summable
  intro k
  rw [Real.norm_eq_abs, sq_abs]
  exact pow_le_pow_left₀ (hf k).1 (hf k).2 2

def s : E := ⟨fun k => if k = 1 then 0 else w k, memlp_of_bounds _ (by
  intro k
  split_ifs
  · exact ⟨le_rfl, le_of_lt (w_pos k)⟩
  · exact ⟨le_of_lt (w_pos k), le_rfl⟩)⟩
def t (N : Set ℕ+) : E := ⟨fun k => if k ∈ N then w k else 0, memlp_of_bounds _ (by
  intro k
  split_ifs
  · exact ⟨le_of_lt (w_pos k), le_rfl⟩
  · exact ⟨le_rfl, le_of_lt (w_pos k)⟩)⟩
lemma s_apply (k : ℕ+) : s k = if k = 1 then 0 else w k := rfl
lemma t_apply (N : Set ℕ+) (k : ℕ+) : t N k = if k ∈ N then w k else 0 := rfl

def p₁ : E := (1-α/2) • e 1 + s
def p₂ (N : Set ℕ+) : E := e 1 + t N
def p₃ (N : Set ℕ+) : E := (α/2) • e 1 + s - t N
def code (N : Set ℕ+) : Finset E := {0,p₁,p₂ N,p₃ N}

lemma one_not_mem (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) : (1 : ℕ+) ∉ N := by
  intro h
  have hi := hN.summable.le_tsum (⟨1,h⟩ : N) (fun k _ => by positivity)
  rw [hN.tsum_eq] at hi
  norm_num at hi
  linarith [alpha_bounds.2]

@[simp] lemma e_apply (i k : ℕ+) : e i k = if k = i then 1 else 0 := by
  simp [e, Pi.single_apply]
@[simp] lemma p₁_apply (k : ℕ+) : p₁ k = if k = 1 then c else w k := by
  change (1-α/2) * e 1 k + s k = _
  by_cases hk : k = 1 <;> simp [s_apply, hk, c]
lemma p₂_apply (N : Set ℕ+) (h1 : (1 : ℕ+) ∉ N) (k : ℕ+) :
    p₂ N k = if k = 1 then 1 else if k ∈ N then w k else 0 := by
  by_cases hk : k = 1 <;> simp [p₂, t_apply, hk, h1]
lemma p₃_apply (N : Set ℕ+) (h1 : (1 : ℕ+) ∉ N) (k : ℕ+) :
    p₃ N k = if k = 1 then α/2 else if k ∈ N then 0 else w k := by
  change (α/2) * e 1 k + s k - t N k = _
  by_cases hk : k = 1
  · simp [s_apply, t_apply, hk, h1]
  · by_cases hn : k ∈ N <;> simp [s_apply, t_apply, hk, hn]

lemma printed_mem (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) :
    ∀ x ∈ code N, x ∈ H := by
  have h1 := one_not_mem N hN
  intro x hx
  simp only [code, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · intro k; exact ⟨by simp, by simpa using (w_pos k).le⟩
  · intro k; rw [p₁_apply]; split_ifs with hk
    · subst k; norm_num [w]; exact ⟨constants.1.le, by linarith [constants.2.1]⟩
    · exact ⟨(w_pos k).le, le_rfl⟩
  · intro k; rw [p₂_apply N h1]; split_ifs with hk hn
    · subst k; norm_num [w]
    · exact ⟨(w_pos k).le, le_rfl⟩
    · exact ⟨le_rfl, (w_pos k).le⟩
  · intro k; rw [p₃_apply N h1]; split_ifs with hk hn
    · subst k; norm_num [w]; constructor <;> linarith [alpha_bounds.1, alpha_bounds.2]
    · exact ⟨le_rfl, (w_pos k).le⟩
    · exact ⟨(w_pos k).le, le_rfl⟩

#eval Lean.versionString
#print axioms alpha_sq
#print axioms alpha_bounds
#print axioms constants
#print axioms hasSum_weights
#print axioms memlp_of_bounds
#print axioms printed_mem
end HilbertCode
```

### `HilbertDistances.lean`

```lean
import HilbertDefinitions

set_option linter.unusedSimpArgs false
noncomputable section
namespace HilbertCode
attribute [local instance] Classical.propDecidable
local instance : DecidableEq E := Classical.decEq _

lemma hasSum_sq_dist (x y : E) :
    HasSum (fun k : ℕ+ => (x k - y k)^2) (dist x y ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (x-y)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
    sq_abs, lp.coeFn_sub, Pi.sub_apply, dist_eq_norm] using h
lemma dist_sq_eq_tsum (x y : E) : dist x y ^ 2 = ∑' k : ℕ+, (x k-y k)^2 :=
  (hasSum_sq_dist x y).tsum_eq.symm

def tail (k : ℕ+) : ℝ := if k = 1 then 0 else w k^2
def part (N : Set ℕ+) (k : ℕ+) : ℝ := if k ∈ N then w k^2 else 0
lemma hasSum_tail : HasSum tail T := by
  convert hasSum_weights.sub (hasSum_ite_eq (1 : ℕ+) (1 : ℝ)) using 1
  · funext k
    by_cases hk : k = 1 <;> simp [tail, hk, w]
  · rfl
lemma hasSum_N (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) :
    HasSum (part N) (α-1) := by
  have h := (hasSum_subtype_iff_indicator (s := N)
    (f := fun k : ℕ+ => 1 / (k : ℝ)^2) (a := α-1)).1 hN
  convert h using 1
  funext k
  by_cases hk : k ∈ N <;> simp [part, hk, w, div_pow]
lemma hasSum_complement (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) :
    HasSum (fun k : ℕ+ => if k=1 ∨ k∈N then 0 else w k^2) (T-(α-1)) := by
  have h1 := one_not_mem N hN
  convert hasSum_tail.sub (hasSum_N N hN) using 1
  funext k
  by_cases hk : k = 1
  · subst k; simp [tail, part, h1]
  · by_cases hn : k ∈ N <;> simp [tail, part, hk, hn]

lemma distance_01 : dist (0 : E) p₁ ^ 2 = q := by
  have h : HasSum (fun k : ℕ+ => ((0 : E) k - p₁ k)^2) (c^2 + T) := by
    convert (hasSum_ite_eq (1 : ℕ+) (c^2)).add hasSum_tail using 1
    funext k
    by_cases hk : k=1 <;> simp [p₁_apply, tail, hk]
  have hh := (hasSum_sq_dist (0 : E) p₁).unique h
  linarith [constants.2.2.2.2.1]
lemma distance_02 (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) :
    dist (0 : E) (p₂ N) ^ 2 = α := by
  have h1 := one_not_mem N hN
  have h : HasSum (fun k : ℕ+ => ((0 : E) k - p₂ N k)^2) (1 + (α-1)) := by
    convert (hasSum_ite_eq (1 : ℕ+) (1 : ℝ)).add (hasSum_N N hN) using 1
    funext k
    by_cases hk : k=1
    · subst k; simp [p₂_apply N h1, part, h1]
    · by_cases hn : k∈N <;> simp [p₂_apply N h1, part, hk, hn]
  have hh := (hasSum_sq_dist (0 : E) (p₂ N)).unique h
  linarith
lemma distance_03 (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) :
    dist (0 : E) (p₃ N) ^ 2 = q := by
  have h1 := one_not_mem N hN
  have h : HasSum (fun k : ℕ+ => ((0 : E) k - p₃ N k)^2)
      ((α/2)^2 + (T-(α-1))) := by
    convert (hasSum_ite_eq (1 : ℕ+) ((α/2)^2)).add (hasSum_complement N hN) using 1
    funext k
    by_cases hk : k=1
    · subst k; simp [p₃_apply N h1]
    · by_cases hn : k∈N <;> simp [p₃_apply N h1, hk, hn]
  have hh := (hasSum_sq_dist (0 : E) (p₃ N)).unique h
  dsimp [T, q] at *
  nlinarith [alpha_sq]
lemma distance_12 (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) :
    dist p₁ (p₂ N) ^ 2 = q := by
  have h1 := one_not_mem N hN
  have h : HasSum (fun k : ℕ+ => (p₁ k - p₂ N k)^2)
      ((c-1)^2 + (T-(α-1))) := by
    convert (hasSum_ite_eq (1 : ℕ+) ((c-1)^2)).add (hasSum_complement N hN) using 1
    funext k
    by_cases hk : k=1
    · subst k; simp [p₁_apply, p₂_apply N h1]
    · by_cases hn : k∈N <;> simp [p₁_apply, p₂_apply N h1, hk, hn]
  have hh := (hasSum_sq_dist p₁ (p₂ N)).unique h
  dsimp [T, q, c] at *
  nlinarith [alpha_sq]
lemma distance_13 (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) :
    dist p₁ (p₃ N) ^ 2 = q := by
  have h1 := one_not_mem N hN
  have h : HasSum (fun k : ℕ+ => (p₁ k - p₃ N k)^2)
      ((c-α/2)^2 + (α-1)) := by
    convert (hasSum_ite_eq (1 : ℕ+) ((c-α/2)^2)).add (hasSum_N N hN) using 1
    funext k
    by_cases hk : k=1
    · subst k; simp [p₁_apply, p₃_apply N h1, part, h1]
    · by_cases hn : k∈N <;> simp [p₁_apply, p₃_apply N h1, part, hk, hn]
  have hh := (hasSum_sq_dist p₁ (p₃ N)).unique h
  dsimp [q, c] at *
  nlinarith
lemma distance_23 (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) :
    dist (p₂ N) (p₃ N) ^ 2 = q := by
  have h1 := one_not_mem N hN
  have h : HasSum (fun k : ℕ+ => (p₂ N k - p₃ N k)^2) ((1-α/2)^2 + T) := by
    convert (hasSum_ite_eq (1 : ℕ+) ((1-α/2)^2)).add hasSum_tail using 1
    funext k
    by_cases hk : k=1
    · subst k; simp [p₂_apply N h1, p₃_apply N h1, tail]
    · by_cases hn : k∈N <;> simp [p₂_apply N h1, p₃_apply N h1, tail, hk, hn]
  have hh := (hasSum_sq_dist (p₂ N) (p₃ N)).unique h
  dsimp [T, q] at *
  nlinarith [alpha_sq]

lemma printed_card (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) :
    (code N).card = 4 := by
  have hq := constants.2.2.1
  have ha := alpha_bounds.1
  have h01 : (0 : E) ≠ p₁ := by
    intro h; have hh := distance_01; rw [h, dist_self] at hh; norm_num at hh; linarith
  have h02 : (0 : E) ≠ p₂ N := by
    intro h; have hh := distance_02 N hN; rw [h, dist_self] at hh; norm_num at hh; linarith
  have h03 : (0 : E) ≠ p₃ N := by
    intro h; have hh := distance_03 N hN; rw [h, dist_self] at hh; norm_num at hh; linarith
  have h12 : p₁ ≠ p₂ N := by
    intro h; have hh := distance_12 N hN; rw [h, dist_self] at hh; norm_num at hh; linarith
  have h13 : p₁ ≠ p₃ N := by
    intro h; have hh := distance_13 N hN; rw [h, dist_self] at hh; norm_num at hh; linarith
  have h23 : p₂ N ≠ p₃ N := by
    intro h; have hh := distance_23 N hN; rw [h, dist_self] at hh; norm_num at hh; linarith
  simp [code, h01, h02, h03, h12, h13, h23]

lemma printed_separation (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ)^2) (α-1)) :
    ∀ x ∈ code N, ∀ y ∈ code N, x ≠ y → q ≤ dist x y ^ 2 := by
  have h10 : dist p₁ (0 : E)^2 = q := by rw [dist_comm, distance_01]
  have h20 : dist (p₂ N) (0 : E)^2 = α := by rw [dist_comm, distance_02 N hN]
  have h30 : dist (p₃ N) (0 : E)^2 = q := by rw [dist_comm, distance_03 N hN]
  have h21 : dist (p₂ N) p₁^2 = q := by rw [dist_comm, distance_12 N hN]
  have h31 : dist (p₃ N) p₁^2 = q := by rw [dist_comm, distance_13 N hN]
  have h32 : dist (p₃ N) (p₂ N)^2 = q := by rw [dist_comm, distance_23 N hN]
  intro x hx y hy hxy
  simp only [code, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    first
    | exact (hxy rfl).elim
    | simpa only [h10, h20, h30, h21, h31, h32, distance_01, distance_02 N hN,
        distance_03 N hN, distance_12 N hN, distance_13 N hN, distance_23 N hN]
        using constants.2.2.2.1.le
    | simpa only [h10, h20, h30, h21, h31, h32, distance_01, distance_02 N hN,
        distance_03 N hN, distance_12 N hN, distance_13 N hN, distance_23 N hN]
        using (le_rfl : q ≤ q)

#print axioms printed_card
#print axioms printed_separation
#print axioms hasSum_sq_dist
#print axioms distance_01
#print axioms distance_02
#print axioms distance_03
#print axioms distance_12
#print axioms distance_13
#print axioms distance_23
end HilbertCode
```

### `HilbertScalar.lean`

```lean
import HilbertDefinitions

noncomputable section
namespace HilbertCode

def W (a b c d : ℝ) := (a-b)^2+(a-c)^2+2*(b-c)^2+(b-d)^2+(c-d)^2

lemma box_bound (w a b c d : ℝ)
    (ha : 0 ≤ a ∧ a ≤ w) (hb : 0 ≤ b ∧ b ≤ w)
    (hc : 0 ≤ c ∧ c ≤ w) (hd : 0 ≤ d ∧ d ≤ w) : W a b c d ≤ 4*w^2 := by
  have hw : 0 ≤ w := ha.1.trans ha.2
  rcases eq_or_lt_of_le hw with he | hp
  · have he' : w = 0 := he.symm
    have : a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    rcases this with ⟨rfl,rfl,rfl,rfl⟩
    simp [W, he']
  · obtain ⟨ha0, haw⟩ := ha
    obtain ⟨hb0, hbw⟩ := hb
    obtain ⟨hc0, hcw⟩ := hc
    obtain ⟨hd0, hdw⟩ := hd
    have hwa : 0 ≤ w-a := by linarith
    have hwb : 0 ≤ w-b := by linarith
    have hwc : 0 ≤ w-c := by linarith
    have hwd : 0 ≤ w-d := by linarith
    have hwad : 0 ≤ 2*w-a-d := by linarith
    have hA : 0 ≤ 2*(w-b)*(w-c)*(2*w-a-d) := by positivity
    have hB : 0 ≤ 2*b*c*(a+d) := by positivity
    have hC : 0 ≤ 2*w*a*(w-a) := by positivity
    have hD : 0 ≤ 4*w*b*(w-b) := by positivity
    have hE : 0 ≤ 4*w*c*(w-c) := by positivity
    have hF : 0 ≤ 2*w*d*(w-d) := by positivity
    have hid : w*(4*w^2-W a b c d) =
        2*(w-b)*(w-c)*(2*w-a-d)+2*b*c*(a+d)+
        2*w*a*(w-a)+4*w*b*(w-b)+4*w*c*(w-c)+2*w*d*(w-d) := by
      unfold W; ring
    nlinarith

lemma cutoff_bound (a b : ℝ) (ha : c ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1-c) : W 0 a b 1 ≤ W 0 c (1-c) 1 := by
  have hD : 0 ≤ 1-2*c := by linarith [constants.2.1]
  have hA : 0 ≤ a-c := by linarith
  have hB : 0 ≤ 1-c-b := by linarith
  have hAB : 0 ≤ (a-c)+(1-c-b) := by linarith
  have hp1 := mul_nonneg hD hAB
  have hp2 := mul_nonneg (sub_nonneg.mpr hab) hAB
  have hp3 := mul_nonneg hA hB
  have hid : W 0 c (1-c) 1 - W 0 a b 1 =
      2*(1-2*c)*((a-c)+(1-c-b)) +
      4*(b-a)*((a-c)+(1-c-b))+4*(a-c)*(1-c-b) := by unfold W; ring
  linarith

lemma ordered_bound (a b d e : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbd : b ≤ d) (hde : d ≤ e) (he : e ≤ 1)
    (hleft : c < b-a) (hright : c < e-d) : W a b d e ≤ W 0 c (1-c) 1 := by
  have h01 : (a-b)^2 ≤ b^2 := by
    nlinarith [mul_nonneg ha (show 0 ≤ 2*b-a by linarith)]
  have h02 : (a-d)^2 ≤ d^2 := by
    nlinarith [mul_nonneg ha (show 0 ≤ 2*d-a by linarith)]
  have h13 : (b-e)^2 ≤ (b-1)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-e by linarith) (show 0 ≤ 1+e-2*b by linarith)]
  have h23 : (d-e)^2 ≤ (d-1)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-e by linarith) (show 0 ≤ 1+e-2*d by linarith)]
  have hn : W a b d e ≤ W 0 b d 1 := by dsimp [W]; nlinarith
  exact hn.trans (cutoff_bound b d (by linarith) hbd (by linarith))

lemma weighted_constants : W 0 c (1-c) 1 + 4*T = 6*q := by
  have h := constants.2.2.2.2.2
  dsimp [W]
  nlinarith

#print axioms box_bound
#print axioms cutoff_bound
#print axioms ordered_bound
end HilbertCode
```

### `HilbertOptimality.lean`

```lean
import HilbertDistances
import HilbertScalar
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.EquivFin

set_option linter.unusedSimpArgs false
noncomputable section
namespace HilbertCode
attribute [local instance] Classical.propDecidable
local instance : DecidableEq E := Classical.decEq _

lemma sorted_enumeration (C : Finset E) (hC : C.card=4) :
    ∃ x : Fin 4 → E, Function.Injective x ∧
      (∀ u, u ∈ C ↔ ∃ i, x i = u) ∧ Monotone (fun i => x i 1) := by
  let en : Fin 4 ≃ C := (Finset.equivFinOfCardEq hC).symm
  let g : Fin 4 → E := fun i => (en i).val
  let σ := Tuple.sort (fun i => g i 1)
  let x : Fin 4 → E := g ∘ σ
  have hg : Function.Injective g := Subtype.val_injective.comp en.injective
  refine ⟨x, hg.comp σ.injective, ?_, ?_⟩
  · intro u
    constructor
    · intro hu
      refine ⟨σ.symm (en.symm ⟨u,hu⟩), ?_⟩
      simp [x, g]
    · rintro ⟨i,rfl⟩
      exact (en (σ i)).property
  · exact Tuple.monotone_sort (fun i => g i 1)

lemma tail_bound (x y : E) (hx : x ∈ H) (hy : y ∈ H) :
    dist x y^2 ≤ (x 1-y 1)^2 + T := by
  have hsum := (hasSum_ite_eq (1 : ℕ+) ((x 1-y 1)^2)).add hasSum_tail
  apply hasSum_le _ (hasSum_sq_dist x y) hsum
  intro k
  by_cases hk : k=1
  · subst k; simp [tail]
  · simp only [tail, ite_eq_right hk, zero_add]
    have h := hx k
    have h' := hy k
    have hp := mul_nonneg (show 0 ≤ w k - (x k-y k) by linarith)
      (show 0 ≤ w k + (x k-y k) by linarith)
    nlinarith

lemma weighted_bound (x : Fin 4 → E) (hx : ∀ i, x i ∈ H) :
    dist (x 0) (x 1)^2 + dist (x 0) (x 2)^2 +
    2*dist (x 1) (x 2)^2 + dist (x 1) (x 3)^2 + dist (x 2) (x 3)^2 ≤
    W (x 0 1) (x 1 1) (x 2 1) (x 3 1) + 4*T := by
  have hsum := ((((hasSum_sq_dist (x 0) (x 1)).add (hasSum_sq_dist (x 0) (x 2))).add
    ((hasSum_sq_dist (x 1) (x 2)).mul_left 2)).add (hasSum_sq_dist (x 1) (x 3))).add
      (hasSum_sq_dist (x 2) (x 3))
  have hmajor := (hasSum_ite_eq (1 : ℕ+) (W (x 0 1) (x 1 1) (x 2 1) (x 3 1))).add
    (hasSum_tail.mul_left 4)
  apply hasSum_le _ hsum hmajor
  intro k
  change W (x 0 k) (x 1 k) (x 2 k) (x 3 k) ≤ _
  by_cases hk : k=1
  · subst k; simp [tail]
  · simpa [hk, tail] using box_bound (w k) _ _ _ _ (hx 0 k) (hx 1 k) (hx 2 k) (hx 3 k)

lemma sorted_pair_bound (x : Fin 4 → E) (hx : ∀ i, x i ∈ H)
    (hs : Monotone (fun i => x i 1)) :
    ∃ i j, i ≠ j ∧ dist (x i) (x j)^2 ≤ q := by
  have h01 := hs (show (0 : Fin 4) ≤ 1 by decide)
  have h12 := hs (show (1 : Fin 4) ≤ 2 by decide)
  have h23 := hs (show (2 : Fin 4) ≤ 3 by decide)
  have hc := constants.1.le
  have hid := constants.2.2.2.2.1
  by_cases hl : x 1 1 - x 0 1 ≤ c
  · refine ⟨0, 1, by decide, ?_⟩
    have hb := tail_bound (x 0) (x 1) (hx 0) (hx 1)
    have hp := (sq_le_sq₀ (sub_nonneg.mpr h01) hc).2 hl
    nlinarith
  by_cases hr : x 3 1 - x 2 1 ≤ c
  · refine ⟨2, 3, by decide, ?_⟩
    have hb := tail_bound (x 2) (x 3) (hx 2) (hx 3)
    have hp := (sq_le_sq₀ (sub_nonneg.mpr h23) hc).2 hr
    nlinarith
  have hw := weighted_bound x hx
  have ho := ordered_bound (x 0 1) (x 1 1) (x 2 1) (x 3 1)
    (hx 0 1).1 h01 h12 h23 (by simpa [w] using (hx 3 1).2)
    (lt_of_not_ge hl) (lt_of_not_ge hr)
  by_contra hn
  push Not at hn
  have hh01 := hn 0 1 (by decide)
  have hh02 := hn 0 2 (by decide)
  have hh12 := hn 1 2 (by decide)
  have hh13 := hn 1 3 (by decide)
  have hh23 := hn 2 3 (by decide)
  linarith [weighted_constants]

lemma competitor_bound (C : Finset E) (hC : C.card=4) (hH : ∀ x ∈ C, x ∈ H) :
    ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ dist u v^2 ≤ q := by
  obtain ⟨x, hi, hm, hs⟩ := sorted_enumeration C hC
  have hx : ∀ i, x i ∈ C := fun i => (hm (x i)).2 ⟨i,rfl⟩
  obtain ⟨i,j,hij,hb⟩ := sorted_pair_bound x (fun i => hH _ (hx i)) hs
  exact ⟨x i, hx i, x j, hx j, (fun he => hij (hi he)), hb⟩

theorem conj27 (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ) ^ 2) (α - 1)) :
    let C : Finset E := {0, (1 - α/2) • e 1 + s, e 1 + t N, (α/2) • e 1 + s - t N}
    C.card = 4 ∧ (∀ x ∈ C, x ∈ H) ∧
    ∀ C' : Finset E, C'.card = 4 → (∀ x ∈ C', x ∈ H) →
      ∃ u ∈ C', ∃ v ∈ C', u ≠ v ∧ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → dist u v ≤ dist x y := by
  change (code N).card = 4 ∧ (∀ x ∈ code N, x ∈ H) ∧ _
  refine ⟨printed_card N hN, printed_mem N hN, ?_⟩
  intro C' hC' hH
  obtain ⟨u,hu,v,hv,huv,hb⟩ := competitor_bound C' hC' hH
  refine ⟨u,hu,v,hv,huv,?_⟩
  intro x hx y hy hxy
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).1
    (hb.trans (printed_separation N hN x hx y hy hxy))

#check conj27
#print axioms sorted_enumeration
#print axioms tail_bound
#print axioms weighted_bound
#print axioms sorted_pair_bound
#print axioms competitor_bound
#print axioms conj27
end HilbertCode
```
