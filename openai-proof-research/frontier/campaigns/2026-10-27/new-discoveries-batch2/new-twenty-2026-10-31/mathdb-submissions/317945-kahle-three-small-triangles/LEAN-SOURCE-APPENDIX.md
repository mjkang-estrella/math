# Lean source appendix

The modules are listed in import order.

### `KahleBase.lean`

```lean
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

def det2 (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

def triArea (p q r : ℝ × ℝ) : ℝ := |det2 p q r| / 2

def InTri (A B C X : ℝ × ℝ) : Prop :=
  ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ X = a • A + b • B + c • C

namespace Kahle

abbrev Pt := ℝ × ℝ
abbrev Region := Fin 4

def A : Pt := (0, 0)
def B : Pt := (2, 0)
def C : Pt := (0, 2)
def M : Pt := (1, 0)
def L : Pt := (0, 1)
def N : Pt := (1, 1)

def blend (b c : ℝ) (p q r : Pt) : Pt :=
  ((1-b-c)*p.1 + b*q.1 + c*r.1, (1-b-c)*p.2 + b*q.2 + c*r.2)

def Hull (p q r x : Pt) : Prop :=
  ∃ b c : ℝ, 0 ≤ b ∧ 0 ≤ c ∧ b + c ≤ 1 ∧ x = blend b c p q r

theorem hull_iff_inTri (p q r x : Pt) : Hull p q r x ↔ InTri p q r x := by
  constructor
  · rintro ⟨b, c, hb, hc, hbc, rfl⟩
    refine ⟨1-b-c, b, c, by linarith, hb, hc, by ring, ?_⟩
    rfl
  · rintro ⟨a, b, c, ha, hb, hc, habc, rfl⟩
    have : a = 1-b-c := by linarith
    subst a
    exact ⟨b, c, hb, hc, by linarith, rfl⟩

def standard (p : Pt) : Prop := 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 2

def sector (i : Region) (p : Pt) : Prop :=
  standard p ∧
    (if i = 0 then p.1 + p.2 ≤ 1
     else if i = 1 then 1 ≤ p.1
     else if i = 2 then 1 ≤ p.2
     else p.1 ≤ 1 ∧ p.2 ≤ 1 ∧ 1 ≤ p.1 + p.2)

def vertices (i : Region) : Pt × Pt × Pt :=
  if i = 0 then (A,M,L)
  else if i = 1 then (B,M,N)
  else if i = 2 then (C,L,N)
  else (M,L,N)

theorem standard_hull {x : Pt} (h : standard x) : Hull A B C x := by
  obtain ⟨hx, hy, hxy⟩ := h
  exact ⟨x.1/2, x.2/2, by linarith, by linarith, by linarith, by
    ext <;> simp [blend,A,B,C]⟩

theorem sector_hull {i : Region} {x : Pt} (h : sector i x) :
    Hull (vertices i).1 (vertices i).2.1 (vertices i).2.2 x := by
  rcases h with ⟨⟨hx,hy,hxy⟩, h⟩
  fin_cases i
  · change x.1 + x.2 ≤ 1 at h
    refine ⟨x.1, x.2, hx, hy, h, ?_⟩
    ext <;> simp [vertices,blend,A,M,L]
  · change 1 ≤ x.1 at h
    refine ⟨2-x.1-x.2, x.2, by linarith, hy, by linarith, ?_⟩
    ext <;> norm_num [vertices,blend,B,M,N]; ring
  · change 1 ≤ x.2 at h
    refine ⟨2-x.1-x.2, x.1, by linarith, hx, by linarith, ?_⟩
    ext <;> norm_num [vertices,blend,C,L,N]; ring
  · change x.1 ≤ 1 ∧ x.2 ≤ 1 ∧ 1 ≤ x.1+x.2 at h
    obtain ⟨h₁,h₂,h₃⟩ := h
    refine ⟨1-x.1, x.1+x.2-1, by linarith, by linarith, by linarith, ?_⟩
    ext <;> norm_num [vertices,blend,M,L,N]

theorem sector_cover {x : Pt} (h : standard x) : ∃ i, sector i x := by
  by_cases ha : x.1+x.2 ≤ 1
  · exact ⟨0,h,ha⟩
  by_cases hb : 1 ≤ x.1
  · exact ⟨1,h,hb⟩
  by_cases hc : 1 ≤ x.2
  · exact ⟨2,h,hc⟩
  exact ⟨3,h,le_of_lt (lt_of_not_ge hb),le_of_lt (lt_of_not_ge hc),le_of_lt (lt_of_not_ge ha)⟩

def Affine (f : Pt → ℝ) : Prop :=
  ∀ b c p q r, f (blend b c p q r) = (1-b-c)*f p + b*f q + c*f r

theorem hull_upper {f : Pt → ℝ} (hf : Affine f) {p q r x : Pt} (hx : Hull p q r x)
    {u : ℝ} (hp : f p ≤ u) (hq : f q ≤ u) (hr : f r ≤ u) : f x ≤ u := by
  obtain ⟨b,c,hb,hc,hbc,rfl⟩ := hx
  have ha : 0 ≤ 1-b-c := by linarith
  rw [hf]
  calc
    _ ≤ (1-b-c)*u + b*u + c*u :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb))
        (mul_le_mul_of_nonneg_left hr hc)
    _ = u := by ring

theorem hull_lower {f : Pt → ℝ} (hf : Affine f) {p q r x : Pt} (hx : Hull p q r x)
    {u : ℝ} (hp : u ≤ f p) (hq : u ≤ f q) (hr : u ≤ f r) : u ≤ f x := by
  have hn : Affine (fun x => -f x) := by
    intro b c p q r
    simp only []; rw [hf b c p q r]
    ring
  exact neg_le_neg_iff.mp (hull_upper hn hx (neg_le_neg hp) (neg_le_neg hq) (neg_le_neg hr))

theorem hull_abs {f : Pt → ℝ} (hf : Affine f) {p q r x : Pt} (hx : Hull p q r x)
    {u : ℝ} (hp : |f p| ≤ u) (hq : |f q| ≤ u) (hr : |f r| ≤ u) : |f x| ≤ u := by
  obtain ⟨hp₁,hp₂⟩ := abs_le.mp hp
  obtain ⟨hq₁,hq₂⟩ := abs_le.mp hq
  obtain ⟨hr₁,hr₂⟩ := abs_le.mp hr
  exact abs_le.mpr ⟨hull_lower hf hx hp₁ hq₁ hr₁, hull_upper hf hx hp₂ hq₂ hr₂⟩

theorem det_left (q r : Pt) : Affine (fun p => det2 p q r) := by
  intro b c p₁ p₂ p₃
  simp only [det2,blend]
  ring
theorem det_middle (p r : Pt) : Affine (fun q => det2 p q r) := by
  intro b c q₁ q₂ q₃
  simp only [det2,blend]
  ring
theorem det_right (p q : Pt) : Affine (det2 p q) := by
  intro b c r₁ r₂ r₃
  simp only [det2,blend]
  ring

theorem det_swap (p q r : Pt) : det2 q p r = -det2 p q r := by unfold det2; ring
theorem det_cycle (p q r : Pt) : det2 q r p = det2 p q r := by unfold det2; ring
theorem abs_swap (p q r : Pt) : |det2 q p r| = |det2 p q r| := by rw [det_swap, abs_neg]
theorem abs_cycle (p q r : Pt) : |det2 q r p| = |det2 p q r| := by rw [det_cycle]

def Small (p q r : Pt) : Prop := |det2 p q r| ≤ 1

theorem small_swap (p q r : Pt) : Small q p r ↔ Small p q r := by
  unfold Small
  rw [abs_swap]

theorem small_cycle (p q r : Pt) : Small q r p ↔ Small p q r := by
  unfold Small
  rw [abs_cycle]

theorem small_swap_right (p q r : Pt) : Small p r q ↔ Small p q r :=
  (small_cycle q p r).trans (small_swap p q r)

def rotate (p : Pt) : Pt := (2-p.1-p.2,p.1)
def reflect (p : Pt) : Pt := (p.2,p.1)

def rotateRegion (i : Region) : Region := if i = 2 then 0 else if i = 3 then 3 else i+1
def reflectRegion (i : Region) : Region := if i = 1 then 2 else if i = 2 then 1 else i

theorem rotate_sector {i : Region} {p : Pt} (h : sector i p) :
    sector (rotateRegion i) (rotate p) := by
  obtain ⟨⟨hx,hy,hxy⟩,h⟩ := h
  have hStd : standard (rotate p) :=
    ⟨by change 0 ≤ 2-p.1-p.2; linarith, hx, by change 2-p.1-p.2+p.1 ≤ 2; linarith⟩
  refine ⟨hStd, ?_⟩
  fin_cases i
  · change p.1+p.2 ≤ 1 at h
    change 1 ≤ 2-p.1-p.2
    linarith
  · exact h
  · change 1 ≤ p.2 at h
    change 2-p.1-p.2+p.1 ≤ 1
    linarith
  · change p.1 ≤ 1 ∧ p.2 ≤ 1 ∧ 1 ≤ p.1+p.2 at h
    obtain ⟨h₁,h₂,h₃⟩ := h
    change 2-p.1-p.2 ≤ 1 ∧ p.1 ≤ 1 ∧ 1 ≤ 2-p.1-p.2+p.1
    exact ⟨by linarith, h₁, by linarith⟩

theorem reflect_sector {i : Region} {p : Pt} (h : sector i p) :
    sector (reflectRegion i) (reflect p) := by
  obtain ⟨⟨hx,hy,hxy⟩,h⟩ := h
  refine ⟨⟨hy,hx,by change p.2+p.1 ≤ 2; linarith⟩,?_⟩
  fin_cases i
  · change p.1+p.2 ≤ 1 at h
    change p.2+p.1 ≤ 1
    linarith
  · exact h
  · exact h
  · change p.1 ≤ 1 ∧ p.2 ≤ 1 ∧ 1 ≤ p.1+p.2 at h
    exact ⟨h.2.1,h.1,by change 1 ≤ p.2+p.1; linarith [h.2.2]⟩

theorem rotate_det (p q r : Pt) : det2 (rotate p) (rotate q) (rotate r) = det2 p q r := by
  simp only [det2,rotate]
  ring

theorem reflect_det (p q r : Pt) :
    det2 (reflect p) (reflect q) (reflect r) = -det2 p q r := by
  simp only [det2,reflect]
  ring

/-- Rotate each corner to corner zero. -/
def turn (i : Region) (p : Pt) : Pt :=
  if i = 1 then rotate (rotate p) else if i = 2 then rotate p else p

def turnRegion (i j : Region) : Region :=
  if i = 1 then rotateRegion (rotateRegion j) else if i = 2 then rotateRegion j else j

theorem turn_sector (i : Region) {j : Region} {p : Pt} (h : sector j p) :
    sector (turnRegion i j) (turn i p) := by
  unfold turn turnRegion
  split
  · exact rotate_sector (rotate_sector h)
  · split
    · exact rotate_sector h
    · exact h

theorem turn_det (i : Region) (p q r : Pt) :
    det2 (turn i p) (turn i q) (turn i r) = det2 p q r := by
  unfold turn
  split
  · rw [rotate_det,rotate_det]
  · split
    · rw [rotate_det]
    · rfl

theorem turn_zero {i : Region} (hi : i ≠ 3) : turnRegion i i = 0 := by
  fin_cases i <;> first | rfl | exact (hi rfl).elim

theorem turn_distinct (i : Region) : Function.Injective (turnRegion i) := by
  intro j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

theorem turn_center (i : Region) : turnRegion i 3 = 3 := by
  fin_cases i <;> rfl

end Kahle
```

### `KahlePairs.lean`

```lean
import KahleBase

namespace Kahle

def vertex (v : Pt × Pt × Pt) (j : Fin 3) : Pt :=
  if j = 0 then v.1 else if j = 1 then v.2.1 else v.2.2

theorem hull_upper_vertex {f : Pt → ℝ} (hf : Affine f) {v : Pt × Pt × Pt}
    {p : Pt} (hp : Hull v.1 v.2.1 v.2.2 p) {u : ℝ}
    (hv : ∀ j, f (vertex v j) ≤ u) : f p ≤ u :=
  hull_upper hf hp (hv 0) (hv 1) (hv 2)

theorem hull_lower_vertex {f : Pt → ℝ} (hf : Affine f) {v : Pt × Pt × Pt}
    {p : Pt} (hp : Hull v.1 v.2.1 v.2.2 p) {u : ℝ}
    (hv : ∀ j, u ≤ f (vertex v j)) : u ≤ f p :=
  hull_lower hf hp (hv 0) (hv 1) (hv 2)

theorem hull_abs_vertex {f : Pt → ℝ} (hf : Affine f) {v : Pt × Pt × Pt}
    {p : Pt} (hp : Hull v.1 v.2.1 v.2.2 p) {u : ℝ}
    (hv : ∀ j, |f (vertex v j)| ≤ u) : |f p| ≤ u :=
  hull_abs hf hp (hv 0) (hv 1) (hv 2)

theorem pair_upper {f : Pt → Pt → ℝ} (hf : ∀ q, Affine (fun p => f p q))
    (hg : ∀ p, Affine (f p)) {i : Region} {p q : Pt} (hp : sector i p) (hq : sector i q)
    {u : ℝ} (hv : ∀ j k, f (vertex (vertices i) j) (vertex (vertices i) k) ≤ u) :
    f p q ≤ u :=
  hull_upper_vertex (hf q) (sector_hull hp) fun j =>
    hull_upper_vertex (hg _) (sector_hull hq) (hv j)

theorem pair_abs {f : Pt → Pt → ℝ} (hf : ∀ q, Affine (fun p => f p q))
    (hg : ∀ p, Affine (f p)) {i : Region} {p q : Pt} (hp : sector i p) (hq : sector i q)
    {u : ℝ} (hv : ∀ j k, |f (vertex (vertices i) j) (vertex (vertices i) k)| ≤ u) :
    |f p q| ≤ u :=
  hull_abs_vertex (hf q) (sector_hull hp) fun j =>
    hull_abs_vertex (hg _) (sector_hull hq) (hv j)

theorem center_pair {p q x : Pt} (hp : sector 3 p) (hq : sector 3 q)
    (hx : standard x) : Small p q x := by
  apply pair_abs (fun q => det_left q x) (fun p => det_middle p x) hp hq
  intro j k
  apply hull_abs_vertex (v := (A,B,C)) (det_right _ _) (standard_hull hx)
  intro t
  fin_cases j <;> fin_cases k <;> fin_cases t <;>
    norm_num [vertex,vertices,det2,A,B,C,M,L,N]

theorem corner_fixed {p q : Pt} (hp : sector 0 p) (hq : sector 0 q) :
    Small p q A ∧ Small p q M ∧ Small p q L ∧ Small p q N := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    (apply pair_abs (fun q => det_left q _) (fun p => det_middle p _) hp hq
     intro j k
     fin_cases j <;> fin_cases k <;> norm_num [vertex,vertices,det2,A,B,C,M,L,N])

theorem affine_add {f g : Pt → ℝ} (hf : Affine f) (hg : Affine g) :
    Affine (fun x => f x + g x) := by
  intro b c p q r
  simp only []; rw [hf b c p q r, hg b c p q r]
  ring

theorem affine_sub {f g : Pt → ℝ} (hf : Affine f) (hg : Affine g) :
    Affine (fun x => f x - g x) := by
  intro b c p q r
  simp only []; rw [hf b c p q r, hg b c p q r]
  ring

theorem corner_exclusive {p q : Pt} (hp : sector 0 p) (hq : sector 0 q) :
    Small p q B ∨ Small p q C := by
  have hs : |det2 p q B + det2 p q C| ≤ 2 := by
    apply pair_abs (fun q => affine_add (det_left q B) (det_left q C))
      (fun p => affine_add (det_middle p B) (det_middle p C)) hp hq
    intro j k
    fin_cases j <;> fin_cases k <;> norm_num [vertex,vertices,det2,A,B,C,M,L,N]
  have hd : |det2 p q B - det2 p q C| ≤ 2 := by
    apply pair_abs (fun q => affine_sub (det_left q B) (det_left q C))
      (fun p => affine_sub (det_middle p B) (det_middle p C)) hp hq
    intro j k
    fin_cases j <;> fin_cases k <;> norm_num [vertex,vertices,det2,A,B,C,M,L,N]
  by_contra! h
  obtain ⟨hs₁,hs₂⟩ := abs_le.mp hs
  obtain ⟨hd₁,hd₂⟩ := abs_le.mp hd
  obtain ⟨hb,hc⟩ := h
  unfold Small at hb hc
  rw [abs_le, not_and_or, not_le, not_le] at hb hc
  rcases hb with hb | hb <;> rcases hc with hc | hc <;> linarith

theorem corner_zero_target {p q x : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (hx : sector 0 x) : Small p q x := by
  obtain ⟨ha,hm,hl,_⟩ := corner_fixed hp hq
  exact hull_abs (det_right p q) (sector_hull hx) ha hm hl

theorem corner_center_target {p q x : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (hx : sector 3 x) : Small p q x := by
  obtain ⟨_,hm,hl,hn⟩ := corner_fixed hp hq
  exact hull_abs (det_right p q) (sector_hull hx) hm hl hn

theorem corner_B_target {p q x : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (hx : sector 1 x) (hb : Small p q B) : Small p q x := by
  obtain ⟨_,hm,_,hn⟩ := corner_fixed hp hq
  exact hull_abs (det_right p q) (sector_hull hx) hb hm hn

theorem corner_C_target {p q x : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (hx : sector 2 x) (hc : Small p q C) : Small p q x := by
  obtain ⟨_,_,hl,hn⟩ := corner_fixed hp hq
  exact hull_abs (det_right p q) (sector_hull hx) hc hl hn

theorem corner_B_sign {p q x : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (hx : sector 1 x) (hb : det2 p q B ≤ 1) (h : ¬Small p q x) : det2 p q x < -1 := by
  obtain ⟨_,hm,_,hn⟩ := corner_fixed hp hq
  have hu := hull_upper (det_right p q) (sector_hull hx) hb
    (abs_le.mp hm).2 (abs_le.mp hn).2
  exact lt_of_not_ge fun hl => h (abs_le.mpr ⟨hl,hu⟩)

theorem corner_pair_targets_zero {i j : Region} (hij : i ≠ j) {p q x y : Pt}
    (hp : sector 0 p) (hq : sector 0 q) (hx : sector i x) (hy : sector j y) :
    Small p q x ∨ Small p q y := by
  have hB := fun w (hw : sector 1 w) (hb : Small p q B) => corner_B_target hp hq hw hb
  have hC := fun w (hw : sector 2 w) (hc : Small p q C) => corner_C_target hp hq hw hc
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact Or.inl (corner_zero_target hp hq hx)
    | exact Or.inr (corner_zero_target hp hq hy)
    | exact Or.inl (corner_center_target hp hq hx)
    | exact Or.inr (corner_center_target hp hq hy)
    | exact (corner_exclusive hp hq).imp (hB x hx) (hC y hy)
    | exact (corner_exclusive hp hq).symm.imp (hC x hx) (hB y hy)

theorem turn_small (i : Region) (p q r : Pt) :
    Small (turn i p) (turn i q) (turn i r) ↔ Small p q r := by
  unfold Small
  rw [turn_det]

theorem reflect_small (p q r : Pt) :
    Small (reflect p) (reflect q) (reflect r) ↔ Small p q r := by
  unfold Small
  rw [reflect_det,abs_neg]

theorem same_sector {i : Region} {p q r : Pt}
    (hp : sector i p) (hq : sector i q) (hr : sector i r) : Small p q r := by
  by_cases hi : i = 3
  · subst i
    exact center_pair hp hq hr.1
  have hz := turn_zero hi
  exact (turn_small i p q r).mp (corner_zero_target
    (hz ▸ turn_sector i hp) (hz ▸ turn_sector i hq) (hz ▸ turn_sector i hr))

theorem pair_center_target {i : Region} {p q r : Pt}
    (hp : sector i p) (hq : sector i q) (hr : sector 3 r) : Small p q r := by
  by_cases hi : i = 3
  · subst i
    exact center_pair hp hq hr.1
  have hz := turn_zero hi
  exact (turn_small i p q r).mp (corner_center_target
    (hz ▸ turn_sector i hp) (hz ▸ turn_sector i hq) (turn_center i ▸ turn_sector i hr))

theorem pair_distinct_targets {i j k : Region} (hjk : j ≠ k) {p q x y : Pt}
    (hp : sector i p) (hq : sector i q) (hx : sector j x) (hy : sector k y) :
    Small p q x ∨ Small p q y := by
  by_cases hi : i = 3
  · subst i
    exact Or.inl (center_pair hp hq hx.1)
  have hz := turn_zero hi
  exact (corner_pair_targets_zero ((turn_distinct i).ne hjk)
    (hz ▸ turn_sector i hp) (hz ▸ turn_sector i hq)
    (turn_sector i hx) (turn_sector i hy)).imp
      (turn_small i p q x).mp (turn_small i p q y).mp

end Kahle
```

### `KahleCases.lean`

```lean
import KahlePairs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace Kahle

private theorem corner_coordinates {p : Pt} (hp : sector 0 p) :
    0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1 :=
  ⟨hp.1.1,hp.1.2.1,hp.2⟩

private theorem B_coordinates {p : Pt} (hp : sector 1 p) :
    1 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 2 :=
  ⟨hp.2,hp.1.2.1,hp.1.2.2⟩

noncomputable def slope (p : Pt) : ℝ := p.2 / (2-p.1)

private theorem slope_bounds {p : Pt} (hp : sector 0 p) : 0 ≤ slope p ∧ slope p ≤ 1/2 := by
  obtain ⟨hx,hy,hxy⟩ := corner_coordinates hp
  have h : 0 < 2-p.1 := by linarith
  exact ⟨div_nonneg hy h.le, (div_le_iff₀ h).2 (by linarith)⟩

private theorem slope_det {p q : Pt} (hp : sector 0 p) (hq : sector 0 q) :
    |det2 p q B| = (2-p.1)*(2-q.1)*|slope p-slope q| := by
  obtain ⟨_,hpy,hp⟩ := corner_coordinates hp
  obtain ⟨_,hqy,hq⟩ := corner_coordinates hq
  have h₁ : 0 < 2-p.1 := by linarith
  have h₂ : 0 < 2-q.1 := by linarith
  rw [← abs_of_nonneg (mul_nonneg h₁.le h₂.le), ← abs_mul]
  congr 1
  unfold slope det2 B
  dsimp only
  field_simp [h₁.ne', h₂.ne']; ring

private theorem slope_small {p q : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (h : |slope p-slope q| ≤ 1/4) : Small p q B := by
  obtain ⟨hpx,hpy,hp'⟩ := corner_coordinates hp
  obtain ⟨hqx,hqy,hq'⟩ := corner_coordinates hq
  have h₁ : 0 ≤ 2-p.1 := by linarith
  have h₂ : 0 ≤ 2-q.1 := by linarith
  have hpq : (2-p.1)*(2-q.1) ≤ 4 := by
    calc
      _ ≤ (2:ℝ)*2 := mul_le_mul (by linarith) (by linarith) h₂ (by norm_num)
      _ = 4 := by norm_num
  unfold Small
  rw [slope_det hp hq]
  calc
    _ ≤ (4:ℝ)*(1/4) := mul_le_mul hpq h (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

private theorem adjacent_gap {a b c : ℝ} (ha : 0 ≤ a) (hc : c ≤ 1/2)
    (hab : a ≤ b) (hbc : b ≤ c) : |a-b| ≤ 1/4 ∨ |b-c| ≤ 1/4 := by
  rw [abs_of_nonpos (sub_nonpos.mpr hab),abs_of_nonpos (sub_nonpos.mpr hbc)]
  by_contra! h
  linarith [h.1,h.2]

private theorem one_gap {a b c : ℝ} (ha : 0 ≤ a ∧ a ≤ 1/2)
    (hb : 0 ≤ b ∧ b ≤ 1/2) (hc : 0 ≤ c ∧ c ≤ 1/2) :
    |a-b| ≤ 1/4 ∨ |a-c| ≤ 1/4 ∨ |b-c| ≤ 1/4 := by
  rcases le_total a b with ab | ba
  · rcases le_total b c with bc | cb
    · rcases adjacent_gap ha.1 hc.2 ab bc with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rcases le_total a c with ac | ca
      · rcases adjacent_gap ha.1 hb.2 ac cb with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by rwa [abs_sub_comm]))
      · rcases adjacent_gap hc.1 hb.2 ca ab with h | h
        · exact Or.inr (Or.inl (by rwa [abs_sub_comm]))
        · exact Or.inl h
  · rcases le_total a c with ac | ca
    · rcases adjacent_gap hb.1 hc.2 ba ac with h | h
      · exact Or.inl (by rwa [abs_sub_comm])
      · exact Or.inr (Or.inl h)
    · rcases le_total b c with bc | cb
      · rcases adjacent_gap hb.1 ha.2 bc ca with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl (by rwa [abs_sub_comm]))
      · rcases adjacent_gap hc.1 ha.2 cb ba with h | h
        · exact Or.inr (Or.inr (by rwa [abs_sub_comm]))
        · exact Or.inl (by rwa [abs_sub_comm])

theorem three_corner_B {p q r x : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (hr : sector 0 r) (hx : sector 1 x) :
    Small p q x ∨ Small p r x ∨ Small q r x := by
  rcases one_gap (slope_bounds hp) (slope_bounds hq) (slope_bounds hr) with h | h | h
  · exact Or.inl (corner_B_target hp hq hx (slope_small hp hq h))
  · exact Or.inr (Or.inl (corner_B_target hp hr hx (slope_small hp hr h)))
  · exact Or.inr (Or.inr (corner_B_target hq hr hx (slope_small hq hr h)))

theorem three_same_target {i j : Region} {p q r x : Pt}
    (hp : sector i p) (hq : sector i q) (hr : sector i r) (hx : sector j x) :
    Small p q x ∨ Small p r x ∨ Small q r x := by
  by_cases hi : i = 3
  · subst i
    exact Or.inl (center_pair hp hq hx.1)
  have hz := turn_zero hi
  suffices h :
      Small (turn i p) (turn i q) (turn i x) ∨
      Small (turn i p) (turn i r) (turn i x) ∨
      Small (turn i q) (turn i r) (turn i x) from
    h.imp (turn_small i p q x).mp
      (fun hc => hc.imp (turn_small i p r x).mp (turn_small i q r x).mp)
  have hp' := hz ▸ turn_sector i hp
  have hq' := hz ▸ turn_sector i hq
  have hr' := hz ▸ turn_sector i hr
  have hx' := turn_sector i hx
  generalize turnRegion i j = k at hx'
  fin_cases k
  · exact Or.inl (corner_zero_target hp' hq' hx')
  · exact three_corner_B hp' hq' hr' hx'
  · have hh := three_corner_B (reflect_sector hp') (reflect_sector hq')
      (reflect_sector hr') (reflect_sector hx')
    exact hh.imp (reflect_small _ _ _).mp
      (fun hc => hc.imp (reflect_small _ _ _).mp (reflect_small _ _ _).mp)
  · exact Or.inl (corner_center_target hp' hq' hx')

private theorem ordered_B_bound {p q : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (h : p.2 ≤ q.2) : det2 p q B ≤ 1 := by
  obtain ⟨hpx,hpy,hp'⟩ := corner_coordinates hp
  obtain ⟨hqx,hqy,hq'⟩ := corner_coordinates hq
  have h₁ := mul_nonneg (show 0 ≤ 2-p.1 by linarith) (sub_nonneg.mpr h)
  have h₂ := mul_nonneg (show 0 ≤ 1-p.1+q.1 by linarith) hpy
  unfold det2 B
  dsimp only
  calc
    _ ≤ p.2 := by linear_combination (norm := linarith) h₁ + h₂
    _ ≤ 1 := by linarith

private theorem ordered_A_bound {r s : Pt} (hr : sector 1 r) (hs : sector 1 s)
    (h : r.2 ≤ s.2) : -1 ≤ det2 r s A := by
  obtain ⟨hrx,hry,hr'⟩ := B_coordinates hr
  obtain ⟨hsx,hsy,hs'⟩ := B_coordinates hs
  have h₁ := mul_nonneg (show 0 ≤ r.1 by linarith) (sub_nonneg.mpr h)
  have h₂ := mul_nonneg (show 0 ≤ 1+r.1-s.1 by linarith) hry
  unfold det2 A
  dsimp only
  calc
    -1 ≤ -r.2 := by linarith
    _ ≤ _ := by linear_combination (norm := linarith) h₁ + h₂

private theorem cross_M {p q : Pt} (hp : sector 0 p) (hq : sector 1 q) :
    -1 ≤ det2 p q M := by
  obtain ⟨hpx,hpy,hp'⟩ := corner_coordinates hp
  obtain ⟨hqx,hqy,hq'⟩ := B_coordinates hq
  have h₁ := mul_nonneg (show 0 ≤ 1-p.2 by linarith) (show 0 ≤ 1-q.2 by linarith)
  have h₂ := mul_nonneg (show 0 ≤ 2-q.1-q.2 by linarith) hpy
  have h₃ := mul_nonneg hpx hqy
  unfold det2 M
  dsimp only
  linear_combination (norm := linarith) h₁ + h₂ + h₃

private theorem cross_L_A (p q : Pt) :
    det2 p q L - det2 p q A = q.1-p.1 := by simp only [det2,L,A]; ring
private theorem cross_N_M (p q : Pt) :
    det2 p q N - det2 p q M = q.1-p.1 := by simp only [det2,N,M]; ring
private theorem cross_L_M (p q : Pt) :
    det2 p q L - det2 p q M = q.1+q.2-p.1-p.2 := by simp only [det2,L,M]; ring
private theorem cross_mid (p q : Pt) :
    2*det2 p q M = det2 p q A + det2 p q B := by simp only [det2,M,A,B]; ring

private theorem two_pairs_ordered {p q r s : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (hr : sector 1 r) (hs : sector 1 s) (hpq : p.2 ≤ q.2) (hrs : r.2 ≤ s.2)
    (h₁ : ¬Small p q s) (h₂ : ¬Small q r s) : False := by
  have hPS := corner_B_sign hp hq hs (ordered_B_bound hp hq hpq) h₁
  have hRS : 1 < det2 r s q := by
    have h := corner_B_sign (reflect_sector (rotate_sector (rotate_sector hr)))
      (reflect_sector (rotate_sector (rotate_sector hs)))
      (reflect_sector (rotate_sector (rotate_sector hq))) ?_ ?_
    · rw [reflect_det,rotate_det,rotate_det] at h
      linarith
    · have mapB : reflect (rotate (rotate A)) = B := by norm_num [rotate,reflect,A,B]
      rw [← mapB, reflect_det,rotate_det,rotate_det]
      linarith [ordered_A_bound hr hs hrs]
    · intro hsmall
      exact h₂ ((small_cycle q r s).mp ((turn_small 1 r s q).mp
        ((reflect_small _ _ _).mp hsmall)))
  have hP : det2 q s p < -1 := by rwa [det_cycle p q s]
  have hR : det2 q s r < -1 := by
    rw [det_swap,det_cycle r s q]
    linarith
  have hM := cross_M hq hs
  have hdx : q.1 ≤ s.1 := by
    linarith [(corner_coordinates hq).2.1,(corner_coordinates hq).2.2,(B_coordinates hs).1]
  by_cases hA : -1 ≤ det2 q s A
  · have hL : -1 ≤ det2 q s L := by linarith [cross_L_A q s]
    exact (not_lt_of_ge (hull_lower (det_right q s) (sector_hull hp) hA hM hL)) hP
  · have hB : -1 ≤ det2 q s B := by linarith [cross_mid q s]
    have hN : -1 ≤ det2 q s N := by linarith [cross_N_M q s]
    exact (not_lt_of_ge (hull_lower (det_right q s) (sector_hull hr) hB hM hN)) hR


theorem two_pairs_zero_one {p q r s : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (hr : sector 1 r) (hs : sector 1 s) :
    Small p q r ∨ Small p q s ∨ Small p r s ∨ Small q r s := by
  by_contra! h
  obtain ⟨h₁,h₂,h₃,h₄⟩ := h
  rcases le_total p.2 q.2 with hpq | hqp <;> rcases le_total r.2 s.2 with hrs | hsr
  · exact two_pairs_ordered hp hq hr hs hpq hrs h₂ h₄
  · exact two_pairs_ordered hp hq hs hr hpq hsr h₁ (h₄ ∘ (small_swap_right q r s).mp)
  · exact two_pairs_ordered hq hp hr hs hqp hrs (h₂ ∘ (small_swap p q s).mp) h₃
  · exact two_pairs_ordered hq hp hs hr hqp hsr
      (h₁ ∘ (small_swap p q r).mp) (h₃ ∘ (small_swap_right p r s).mp)

private theorem cross_center {p q o : Pt} (hp : sector 0 p) (hq : sector 1 q)
    (ho : sector 3 o) : -1 ≤ det2 p q o := by
  obtain ⟨hpx,hpy,hp'⟩ := corner_coordinates hp
  obtain ⟨hqx,hqy,hq'⟩ := B_coordinates hq
  have hM := cross_M hp hq
  have hL : -1 ≤ det2 p q L := by linarith [cross_L_M p q]
  have hN : -1 ≤ det2 p q N := by linarith [cross_N_M p q]
  exact hull_lower (det_right p q) (sector_hull ho) hM hL hN

private theorem cross_center_large {p q o : Pt} (hp : sector 0 p) (hq : sector 1 q)
    (ho : sector 3 o) (h : ¬Small p q o) : 1 < det2 p q o :=
  lt_of_not_ge fun hh => h (abs_le.mpr ⟨cross_center hp hq ho, hh⟩)

def edgeDet (p q r s : Pt) : ℝ :=
  (r.1-q.1)*(s.2-p.2) - (r.2-q.2)*(s.1-p.1)

private theorem edge_bound {p q r s : Pt}
    (hp : standard p) (hq : standard q) (hr : standard r) (hs : standard s) :
    |edgeDet p q r s| ≤ 4 := by
  refine hull_abs_vertex (v := (A,B,C)) (f := fun x => edgeDet x q r s) ?_ (standard_hull hp) ?_
  · intro b c u v w
    simp only [edgeDet,blend]
    ring
  intro i
  refine hull_abs_vertex (v := (A,B,C)) (f := fun x => edgeDet (vertex (A,B,C) i) x r s) ?_ (standard_hull hq) ?_
  · intro b c u v w
    simp only [edgeDet,blend]
    ring
  intro j
  refine hull_abs_vertex (v := (A,B,C)) (f := fun x => edgeDet (vertex (A,B,C) i) (vertex (A,B,C) j) x s) ?_ (standard_hull hr) ?_
  · intro b c u v w
    simp only [edgeDet,blend]
    ring
  intro k
  refine hull_abs_vertex (v := (A,B,C)) (f := fun x => edgeDet (vertex (A,B,C) i) (vertex (A,B,C) j) (vertex (A,B,C) k) x) ?_ (standard_hull hs) ?_
  · intro b c u v w
    simp only [edgeDet,blend]
    ring
  intro t
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases t <;>
    norm_num [edgeDet,vertex,A,B,C]

private theorem split_ordered {p q r s o : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (hr : sector 1 r) (hs : sector 2 s) (ho : sector 3 o) (hpq : p.2 ≤ q.2)
    (h₁ : ¬Small p q r) (h₂ : ¬Small q r o) (h₃ : ¬Small q s o)
    (h₄ : ¬Small r s o) : False := by
  have hPQR := corner_B_sign hp hq hr (ordered_B_bound hp hq hpq) h₁
  have hQRO := cross_center_large hq hr ho h₂
  have hSQO : 1 < det2 s q o := by
    have h := cross_center_large (rotate_sector hs) (rotate_sector hq) (rotate_sector ho) ?_
    · rwa [rotate_det] at h
    · intro h
      unfold Small at h
      rw [rotate_det] at h
      exact h₃ ((small_swap q s o).mp h)
  have hRSO : 1 < det2 r s o := by
    have h := cross_center_large (turn_sector 1 hr) (turn_sector 1 hs) (turn_sector 1 ho)
      (h₄ ∘ (turn_small 1 r s o).mp)
    rwa [turn_det] at h
  have hQSO : -1 > det2 q s o := by
    rw [det_swap q s o] at hSQO
    linarith
  have heq : -det2 p q r + det2 q r o - det2 q s o + det2 r s o =
      edgeDet p q r s := by simp only [det2,edgeDet]; ring
  have hb := (abs_le.mp (edge_bound hp.1 hq.1 hr.1 hs.1)).2
  linarith

theorem split_zero_one_two {p q r s o : Pt} (hp : sector 0 p) (hq : sector 0 q)
    (hr : sector 1 r) (hs : sector 2 s) (ho : sector 3 o) :
    Small p q r ∨ Small p r o ∨ Small p s o ∨ Small q r o ∨ Small q s o ∨ Small r s o := by
  by_contra! h
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := h
  rcases le_total p.2 q.2 with hpq | hqp
  · exact split_ordered hp hq hr hs ho hpq h₁ h₄ h₅ h₆
  · exact split_ordered hq hp hr hs ho hqp (h₁ ∘ (small_swap p q r).mp) h₂ h₃ h₆

/-- Relabel the first two chosen distinct corners as zero and one. -/
def orient (i j : Region) (p : Pt) : Pt :=
  if turnRegion i j = 2 then reflect (turn i p) else turn i p

def orientRegion (i j k : Region) : Region :=
  if turnRegion i j = 2 then reflectRegion (turnRegion i k) else turnRegion i k

theorem orient_sector (i j : Region) {k : Region} {p : Pt} (h : sector k p) :
    sector (orientRegion i j k) (orient i j p) := by
  unfold orient orientRegion
  split
  · exact reflect_sector (turn_sector i h)
  · exact turn_sector i h

theorem orient_small (i j : Region) (p q r : Pt) :
    Small (orient i j p) (orient i j q) (orient i j r) ↔ Small p q r := by
  unfold orient
  split
  · exact (reflect_small _ _ _).trans (turn_small i p q r)
  · exact turn_small i p q r

private theorem orient_corners {i j : Region} (hi : i ≠ 3) (hj : j ≠ 3) (hij : i ≠ j) :
    orientRegion i j i = 0 ∧ orientRegion i j j = 1 ∧ orientRegion i j 3 = 3 := by
  revert hi hj hij
  fin_cases i <;> fin_cases j <;> decide

private theorem orient_third {i j k : Region} (hi : i ≠ 3) (hj : j ≠ 3) (hk : k ≠ 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : orientRegion i j k = 2 := by
  revert hi hj hk hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

theorem two_pairs {i j : Region} {p q r s : Pt} (hp : sector i p) (hq : sector i q)
    (hr : sector j r) (hs : sector j s) :
    Small p q r ∨ Small p q s ∨ Small p r s ∨ Small q r s := by
  by_cases hi : i = 3
  · subst i
    exact Or.inl (center_pair hp hq hr.1)
  by_cases hj : j = 3
  · subst j
    exact Or.inr (Or.inr (Or.inl ((small_cycle p r s).mp (center_pair hr hs hp.1))))
  by_cases hij : i = j
  · subst j
    exact Or.inl (same_sector hp hq hr)
  obtain ⟨h0,h1,_⟩ := orient_corners hi hj hij
  have h := two_pairs_zero_one
    (h0 ▸ orient_sector i j hp) (h0 ▸ orient_sector i j hq)
    (h1 ▸ orient_sector i j hr) (h1 ▸ orient_sector i j hs)
  exact h.imp (orient_small i j p q r).mp
    (fun h => h.imp (orient_small i j p q s).mp
      (fun h => h.imp (orient_small i j p r s).mp (orient_small i j q r s).mp))

theorem split_corners {i j k : Region} {p q r s o : Pt}
    (hi : i ≠ 3) (hj : j ≠ 3) (hk : k ≠ 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hp : sector i p) (hq : sector i q) (hr : sector j r) (hs : sector k s) (ho : sector 3 o) :
    Small p q r ∨ Small p r o ∨ Small p s o ∨ Small q r o ∨ Small q s o ∨ Small r s o := by
  obtain ⟨h0,h1,h3⟩ := orient_corners hi hj hij
  have h2 := orient_third hi hj hk hij hik hjk
  have h := split_zero_one_two
    (h0 ▸ orient_sector i j hp) (h0 ▸ orient_sector i j hq)
    (h1 ▸ orient_sector i j hr) (h2 ▸ orient_sector i j hs) (h3 ▸ orient_sector i j ho)
  exact h.imp (orient_small i j p q r).mp
    (fun h => h.imp (orient_small i j p r o).mp
      (fun h => h.imp (orient_small i j p s o).mp
        (fun h => h.imp (orient_small i j q r o).mp
          (fun h => h.imp (orient_small i j q s o).mp (orient_small i j r s o).mp))))

end Kahle
```

### `KahleCounting.lean`

```lean
import KahleCases
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Tauto

namespace Kahle

abbrev Labels := Finset (Fin 5)

def Good (P : Fin 5 → Fin 5 → Fin 5 → Prop) (s : Labels) : Prop :=
  ∃ i j k, i < j ∧ j < k ∧ s = {i,j,k} ∧ P i j k

def Three (P : Fin 5 → Fin 5 → Fin 5 → Prop) : Prop :=
  ∃ s t u : Labels, s ≠ t ∧ s ≠ u ∧ t ≠ u ∧ Good P s ∧ Good P t ∧ Good P u

theorem triple_three {i j k : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ({i,j,k} : Labels).card = 3 :=
  Finset.card_eq_three.mpr ⟨i,j,k,hij,hik,hjk,rfl⟩

theorem good_card {P : Fin 5 → Fin 5 → Fin 5 → Prop} {s : Labels}
    (h : Good P s) : s.card = 3 := by
  obtain ⟨i,j,k,hij,hjk,rfl,-⟩ := h
  exact triple_three hij.ne (hij.trans hjk).ne hjk.ne

theorem count_three {P : Fin 5 → Fin 5 → Fin 5 → Prop}
    [DecidablePred (fun s : Labels => ∃ i j k, i < j ∧ j < k ∧ s = {i,j,k} ∧ P i j k)]
    (h : Three P) :
    3 ≤ ((Finset.univ.powersetCard 3 : Finset Labels).filter
      (fun s => ∃ i j k, i < j ∧ j < k ∧ s = {i,j,k} ∧ P i j k)).card := by
  obtain ⟨s,t,u,hst,hsu,htu,hs,ht,hu⟩ := h
  let F := (Finset.univ.powersetCard 3 : Finset Labels).filter
    (fun s => ∃ i j k, i < j ∧ j < k ∧ s = {i,j,k} ∧ P i j k)
  have hmem (v : Labels) (hv : Good P v) : v ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,good_card hv⟩,hv⟩
  have hsub : ({s,t,u} : Finset Labels) ⊆ F := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with h | h | h
    · exact h.symm ▸ hmem s hs
    · exact h.symm ▸ hmem t ht
    · exact h.symm ▸ hmem u hu
  have hcard : ({s,t,u} : Finset Labels).card = 3 :=
    Finset.card_eq_three.mpr ⟨s,t,u,hst,hsu,htu,rfl⟩
  have hle : ({s,t,u} : Finset Labels).card ≤ F.card := Finset.card_le_card hsub
  simpa only [hcard] using hle

theorem good_of_distinct {P : Fin 5 → Fin 5 → Fin 5 → Prop}
    (sw : ∀ i j k, P i j k → P j i k) (rt : ∀ i j k, P i j k → P i k j)
    {i j k : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (h : P i j k) :
    Good P {i,j,k} := by
  rcases lt_or_gt_of_ne hij with ij | ji
  · rcases lt_or_gt_of_ne hjk with jk | kj
    · exact ⟨i,j,k,ij,jk,rfl,h⟩
    · rcases lt_or_gt_of_ne hik with ik | ki
      · exact ⟨i,k,j,ik,kj,by ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto,rt i j k h⟩
      · exact ⟨k,i,j,ki,ij,by ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto,
          sw i k j (rt i j k h)⟩
  · rcases lt_or_gt_of_ne hik with ik | ki
    · exact ⟨j,i,k,ji,ik,by ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto,sw i j k h⟩
    · rcases lt_or_gt_of_ne hjk with jk | kj
      · exact ⟨j,k,i,jk,ki,by ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto,
          rt j i k (sw i j k h)⟩
      · exact ⟨k,j,i,kj,ji,by ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto,
          sw j k i (rt j i k (sw i j k h))⟩

theorem good_map {P Q : Fin 5 → Fin 5 → Fin 5 → Prop} (e : Fin 5 ≃ Fin 5)
    (sw : ∀ i j k, Q i j k → Q j i k) (rt : ∀ i j k, Q i j k → Q i k j)
    (hPQ : ∀ i j k, P i j k → Q (e i) (e j) (e k)) {s : Labels} (h : Good P s) :
    Good Q (s.map e.toEmbedding) := by
  obtain ⟨i,j,k,hij,hjk,rfl,h⟩ := h
  simp only [Finset.map_insert,Finset.map_singleton,Equiv.toEmbedding_apply]
  exact good_of_distinct sw rt (e.injective.ne hij.ne) (e.injective.ne (hij.trans hjk).ne)
    (e.injective.ne hjk.ne) (hPQ i j k h)

theorem three_map {P Q : Fin 5 → Fin 5 → Fin 5 → Prop} (e : Fin 5 ≃ Fin 5)
    (sw : ∀ i j k, Q i j k → Q j i k) (rt : ∀ i j k, Q i j k → Q i k j)
    (hPQ : ∀ i j k, P i j k → Q (e i) (e j) (e k)) (h : Three P) : Three Q := by
  obtain ⟨s,t,u,hst,hsu,htu,hs,ht,hu⟩ := h
  have inj := Finset.map_injective e.toEmbedding
  exact ⟨s.map e.toEmbedding,t.map e.toEmbedding,u.map e.toEmbedding,
    inj.ne hst,inj.ne hsu,inj.ne htu,good_map e sw rt hPQ hs,
    good_map e sw rt hPQ ht,good_map e sw rt hPQ hu⟩

theorem three_mono {P Q : Fin 5 → Fin 5 → Fin 5 → Prop}
    (hPQ : ∀ i j k, P i j k → Q i j k) (h : Three P) : Three Q := by
  obtain ⟨s,t,u,hst,hsu,htu,hs,ht,hu⟩ := h
  have convert (v : Labels) (hv : Good P v) : Good Q v := by
    obtain ⟨i,j,k,hij,hjk,e,hh⟩ := hv
    exact ⟨i,j,k,hij,hjk,e,hPQ i j k hh⟩
  exact ⟨s,t,u,hst,hsu,htu,convert s hs,convert t ht,convert u hu⟩

theorem ordered_good {P : Fin 5 → Fin 5 → Fin 5 → Prop}
    {i j k : Fin 5} (hij : i < j) (hjk : j < k) (h : P i j k) :
    Good P {i,j,k} := ⟨i,j,k,hij,hjk,rfl,h⟩

end Kahle
```

### `KahleOccupancies.lean`

```lean
import KahleCounting

namespace Kahle

set_option maxHeartbeats 2000000 in
/-- After sorting the region labels, only the four adjacent ties and the
    possible terminal central block matter. Each branch obtains three
    different increasing triples using the geometric disjunctions. -/
theorem sorted_three (p : Fin 5 → Pt) (r : Fin 5 → Region) (hm : Monotone r)
    (hp : ∀ i, sector (r i) (p i)) :
    Three (fun i j k => Small (p i) (p j) (p k)) := by
  have m01 : (r 0).val ≤ (r 1).val := hm (by decide)
  have m12 : (r 1).val ≤ (r 2).val := hm (by decide)
  have m23 : (r 2).val ≤ (r 3).val := hm (by decide)
  have m34 : (r 3).val ≤ (r 4).val := hm (by decide)
  have b4 := (r 4).isLt
  by_cases h01 : (r 0).val = (r 1).val <;> by_cases h12 : (r 1).val = (r 2).val <;>
    by_cases h23 : (r 2).val = (r 3).val <;> by_cases h34 : (r 3).val = (r 4).val <;>
    by_cases c4 : (r 4).val = 3
  all_goals try (exfalso; omega)
  · have s012 : Small (p 0) (p 1) (p 2) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2))
    have s013 : Small (p 0) (p 1) (p 3) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 3 = r 0 from Fin.ext (by omega)) ▸ hp 3))
    have s014 : Small (p 0) (p 1) (p 4) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 4 = r 0 from Fin.ext (by omega)) ▸ hp 4))
    exact ⟨{0,1,2},{0,1,3},{0,1,4},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s012,
      ordered_good (by decide) (by decide) s013,
      ordered_good (by decide) (by decide) s014⟩
  · have s012 : Small (p 0) (p 1) (p 2) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2))
    have s013 : Small (p 0) (p 1) (p 3) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 3 = r 0 from Fin.ext (by omega)) ▸ hp 3))
    have s014 : Small (p 0) (p 1) (p 4) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 4 = r 0 from Fin.ext (by omega)) ▸ hp 4))
    exact ⟨{0,1,2},{0,1,3},{0,1,4},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s012,
      ordered_good (by decide) (by decide) s013,
      ordered_good (by decide) (by decide) s014⟩
  · have s012 : Small (p 0) (p 1) (p 2) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2))
    have s013 : Small (p 0) (p 1) (p 3) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 3 = r 0 from Fin.ext (by omega)) ▸ hp 3))
    have s023 : Small (p 0) (p 2) (p 3) := (same_sector (hp 0) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2) ((show r 3 = r 0 from Fin.ext (by omega)) ▸ hp 3))
    exact ⟨{0,1,2},{0,1,3},{0,2,3},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s012,
      ordered_good (by decide) (by decide) s013,
      ordered_good (by decide) (by decide) s023⟩
  · have s012 : Small (p 0) (p 1) (p 2) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2))
    have s013 : Small (p 0) (p 1) (p 3) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 3 = r 0 from Fin.ext (by omega)) ▸ hp 3))
    have s023 : Small (p 0) (p 2) (p 3) := (same_sector (hp 0) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2) ((show r 3 = r 0 from Fin.ext (by omega)) ▸ hp 3))
    exact ⟨{0,1,2},{0,1,3},{0,2,3},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s012,
      ordered_good (by decide) (by decide) s013,
      ordered_good (by decide) (by decide) s023⟩
  · have s013 : Small (p 0) (p 1) (p 3) := (pair_center_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3))
    have s014 : Small (p 0) (p 1) (p 4) := (pair_center_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    have s012 : Small (p 0) (p 1) (p 2) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2))
    exact ⟨{0,1,3},{0,1,4},{0,1,2},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s013,
      ordered_good (by decide) (by decide) s014,
      ordered_good (by decide) (by decide) s012⟩
  · have s012 : Small (p 0) (p 1) (p 2) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2))
    rcases three_same_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2) (hp 3) with s013 | s023 | s123
    · rcases three_same_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2) (hp 4) with s014 | s024 | s124
      · exact ⟨{0,1,2},{0,1,3},{0,1,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s014⟩
      · exact ⟨{0,1,2},{0,1,3},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s024⟩
      · exact ⟨{0,1,2},{0,1,3},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s124⟩
    · rcases three_same_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2) (hp 4) with s014 | s024 | s124
      · exact ⟨{0,1,2},{0,2,3},{0,1,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s023,
          ordered_good (by decide) (by decide) s014⟩
      · exact ⟨{0,1,2},{0,2,3},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s023,
          ordered_good (by decide) (by decide) s024⟩
      · exact ⟨{0,1,2},{0,2,3},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s023,
          ordered_good (by decide) (by decide) s124⟩
    · rcases three_same_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2) (hp 4) with s014 | s024 | s124
      · exact ⟨{0,1,2},{1,2,3},{0,1,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) s014⟩
      · exact ⟨{0,1,2},{1,2,3},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) s024⟩
      · exact ⟨{0,1,2},{1,2,3},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) s124⟩
  · have s014 : Small (p 0) (p 1) (p 4) := (pair_center_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    have s024 : Small (p 0) (p 2) (p 4) := (pair_center_target (hp 0) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    have s012 : Small (p 0) (p 1) (p 2) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2))
    exact ⟨{0,1,4},{0,2,4},{0,1,2},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s014,
      ordered_good (by decide) (by decide) s024,
      ordered_good (by decide) (by decide) s012⟩
  · have s012 : Small (p 0) (p 1) (p 2) := (same_sector (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2))
    rcases pair_distinct_targets (show r 3 ≠ r 4 from fun h => (show (r 3).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 3) (hp 4) with s013 | s014
    · rcases pair_distinct_targets (show r 3 ≠ r 4 from fun h => (show (r 3).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2) (hp 3) (hp 4) with s023 | s024
      · exact ⟨{0,1,2},{0,1,3},{0,2,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s023⟩
      · exact ⟨{0,1,2},{0,1,3},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s024⟩
    · rcases pair_distinct_targets (show r 3 ≠ r 4 from fun h => (show (r 3).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 2 = r 0 from Fin.ext (by omega)) ▸ hp 2) (hp 3) (hp 4) with s023 | s024
      · exact ⟨{0,1,2},{0,1,4},{0,2,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s023⟩
      · exact ⟨{0,1,2},{0,1,4},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s024⟩
  · have s012 : Small (p 0) (p 1) (p 2) := (pair_center_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 2 = 3 from Fin.ext (by change (r 2).val = 3; omega)) ▸ hp 2))
    have s013 : Small (p 0) (p 1) (p 3) := (pair_center_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3))
    have s234 : Small (p 2) (p 3) (p 4) := (same_sector (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = r 2 from Fin.ext (by omega)) ▸ hp 4))
    exact ⟨{0,1,2},{0,1,3},{2,3,4},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s012,
      ordered_good (by decide) (by decide) s013,
      ordered_good (by decide) (by decide) s234⟩
  · have s234 : Small (p 2) (p 3) (p 4) := (same_sector (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = r 2 from Fin.ext (by omega)) ▸ hp 4))
    rcases three_same_target (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = r 2 from Fin.ext (by omega)) ▸ hp 4) (hp 0) with s023 | s024 | s034
    · rcases three_same_target (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = r 2 from Fin.ext (by omega)) ▸ hp 4) (hp 1) with s123 | s124 | s134
      · exact ⟨{2,3,4},{0,2,3},{1,2,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123)⟩
      · exact ⟨{2,3,4},{0,2,3},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 4)).mp s124)⟩
      · exact ⟨{2,3,4},{0,2,3},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 3) (p 4)).mp s134)⟩
    · rcases three_same_target (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = r 2 from Fin.ext (by omega)) ▸ hp 4) (hp 1) with s123 | s124 | s134
      · exact ⟨{2,3,4},{0,2,4},{1,2,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 4)).mp s024),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123)⟩
      · exact ⟨{2,3,4},{0,2,4},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 4)).mp s024),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 4)).mp s124)⟩
      · exact ⟨{2,3,4},{0,2,4},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 4)).mp s024),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 3) (p 4)).mp s134)⟩
    · rcases three_same_target (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = r 2 from Fin.ext (by omega)) ▸ hp 4) (hp 1) with s123 | s124 | s134
      · exact ⟨{2,3,4},{0,3,4},{1,2,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123)⟩
      · exact ⟨{2,3,4},{0,3,4},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 4)).mp s124)⟩
      · exact ⟨{2,3,4},{0,3,4},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 3) (p 4)).mp s134)⟩
  · have s014 : Small (p 0) (p 1) (p 4) := (pair_center_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    have s234 : Small (p 2) (p 3) (p 4) := (pair_center_target (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    rcases two_pairs (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) with s012 | s013 | s023 | s123
    · exact ⟨{0,1,4},{2,3,4},{0,1,2},by decide,by decide,by decide,
        ordered_good (by decide) (by decide) s014,
        ordered_good (by decide) (by decide) s234,
        ordered_good (by decide) (by decide) s012⟩
    · exact ⟨{0,1,4},{2,3,4},{0,1,3},by decide,by decide,by decide,
        ordered_good (by decide) (by decide) s014,
        ordered_good (by decide) (by decide) s234,
        ordered_good (by decide) (by decide) s013⟩
    · exact ⟨{0,1,4},{2,3,4},{0,2,3},by decide,by decide,by decide,
        ordered_good (by decide) (by decide) s014,
        ordered_good (by decide) (by decide) s234,
        ordered_good (by decide) (by decide) s023⟩
    · exact ⟨{0,1,4},{2,3,4},{1,2,3},by decide,by decide,by decide,
        ordered_good (by decide) (by decide) s014,
        ordered_good (by decide) (by decide) s234,
        ordered_good (by decide) (by decide) s123⟩
  · rcases pair_distinct_targets (show r 0 ≠ r 4 from fun h => (show (r 0).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) (hp 0) (hp 4) with s023 | s234
    · rcases pair_distinct_targets (show r 1 ≠ r 4 from fun h => (show (r 1).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) (hp 1) (hp 4) with s123 | s234
      · rcases pair_distinct_targets (show r 2 ≠ r 4 from fun h => (show (r 2).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) (hp 4) with s012 | s014
        · exact ⟨{0,2,3},{1,2,3},{0,1,2},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
            ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123),
            ordered_good (by decide) (by decide) s012⟩
        · exact ⟨{0,2,3},{1,2,3},{0,1,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
            ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123),
            ordered_good (by decide) (by decide) s014⟩
      · rcases pair_distinct_targets (show r 2 ≠ r 4 from fun h => (show (r 2).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) (hp 4) with s012 | s014
        · exact ⟨{0,2,3},{2,3,4},{0,1,2},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
            ordered_good (by decide) (by decide) s234,
            ordered_good (by decide) (by decide) s012⟩
        · exact ⟨{0,2,3},{2,3,4},{0,1,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
            ordered_good (by decide) (by decide) s234,
            ordered_good (by decide) (by decide) s014⟩
    · rcases pair_distinct_targets (show r 2 ≠ r 4 from fun h => (show (r 2).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) (hp 4) with s012 | s014
      · rcases pair_distinct_targets (show r 3 ≠ r 4 from fun h => (show (r 3).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 3) (hp 4) with s013 | s014
        · exact ⟨{2,3,4},{0,1,2},{0,1,3},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) s234,
            ordered_good (by decide) (by decide) s012,
            ordered_good (by decide) (by decide) s013⟩
        · exact ⟨{2,3,4},{0,1,2},{0,1,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) s234,
            ordered_good (by decide) (by decide) s012,
            ordered_good (by decide) (by decide) s014⟩
      · rcases two_pairs (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) with s012 | s013 | s023 | s123
        · exact ⟨{2,3,4},{0,1,4},{0,1,2},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) s234,
            ordered_good (by decide) (by decide) s014,
            ordered_good (by decide) (by decide) s012⟩
        · exact ⟨{2,3,4},{0,1,4},{0,1,3},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) s234,
            ordered_good (by decide) (by decide) s014,
            ordered_good (by decide) (by decide) s013⟩
        · exact ⟨{2,3,4},{0,1,4},{0,2,3},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) s234,
            ordered_good (by decide) (by decide) s014,
            ordered_good (by decide) (by decide) s023⟩
        · exact ⟨{2,3,4},{0,1,4},{1,2,3},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) s234,
            ordered_good (by decide) (by decide) s014,
            ordered_good (by decide) (by decide) s123⟩
  · have s034 : Small (p 0) (p 3) (p 4) := ((small_cycle (p 0) (p 3) (p 4)).mp (center_pair ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) (hp 0).1))
    have s013 : Small (p 0) (p 1) (p 3) := (pair_center_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3))
    have s014 : Small (p 0) (p 1) (p 4) := (pair_center_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    exact ⟨{0,3,4},{0,1,3},{0,1,4},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s034,
      ordered_good (by decide) (by decide) s013,
      ordered_good (by decide) (by decide) s014⟩
  · rcases pair_distinct_targets (show r 0 ≠ r 2 from fun h => (show (r 0).val ≠ (r 2).val by omega) (congrArg Fin.val h)) (hp 3) ((show r 4 = r 3 from Fin.ext (by omega)) ▸ hp 4) (hp 0) (hp 2) with s034 | s234
    · rcases pair_distinct_targets (show r 1 ≠ r 2 from fun h => (show (r 1).val ≠ (r 2).val by omega) (congrArg Fin.val h)) (hp 3) ((show r 4 = r 3 from Fin.ext (by omega)) ▸ hp 4) (hp 1) (hp 2) with s134 | s234
      · rcases pair_distinct_targets (show r 2 ≠ r 3 from fun h => (show (r 2).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) (hp 3) with s012 | s013
        · exact ⟨{0,3,4},{1,3,4},{0,1,2},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 3) (p 4)).mp s134),
            ordered_good (by decide) (by decide) s012⟩
        · exact ⟨{0,3,4},{1,3,4},{0,1,3},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 3) (p 4)).mp s134),
            ordered_good (by decide) (by decide) s013⟩
      · rcases pair_distinct_targets (show r 2 ≠ r 3 from fun h => (show (r 2).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) (hp 3) with s012 | s013
        · exact ⟨{0,3,4},{2,3,4},{0,1,2},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) ((small_cycle (p 2) (p 3) (p 4)).mp s234),
            ordered_good (by decide) (by decide) s012⟩
        · exact ⟨{0,3,4},{2,3,4},{0,1,3},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) ((small_cycle (p 2) (p 3) (p 4)).mp s234),
            ordered_good (by decide) (by decide) s013⟩
    · rcases pair_distinct_targets (show r 2 ≠ r 3 from fun h => (show (r 2).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) (hp 3) with s012 | s013
      · rcases two_pairs (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 3) ((show r 4 = r 3 from Fin.ext (by omega)) ▸ hp 4) with s013 | s014 | s034 | s134
        · exact ⟨{2,3,4},{0,1,2},{0,1,3},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 2) (p 3) (p 4)).mp s234),
            ordered_good (by decide) (by decide) s012,
            ordered_good (by decide) (by decide) s013⟩
        · exact ⟨{2,3,4},{0,1,2},{0,1,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 2) (p 3) (p 4)).mp s234),
            ordered_good (by decide) (by decide) s012,
            ordered_good (by decide) (by decide) s014⟩
        · exact ⟨{2,3,4},{0,1,2},{0,3,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 2) (p 3) (p 4)).mp s234),
            ordered_good (by decide) (by decide) s012,
            ordered_good (by decide) (by decide) s034⟩
        · exact ⟨{2,3,4},{0,1,2},{1,3,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 2) (p 3) (p 4)).mp s234),
            ordered_good (by decide) (by decide) s012,
            ordered_good (by decide) (by decide) s134⟩
      · rcases pair_distinct_targets (show r 2 ≠ r 4 from fun h => (show (r 2).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) (hp 4) with s012 | s014
        · exact ⟨{2,3,4},{0,1,3},{0,1,2},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 2) (p 3) (p 4)).mp s234),
            ordered_good (by decide) (by decide) s013,
            ordered_good (by decide) (by decide) s012⟩
        · exact ⟨{2,3,4},{0,1,3},{0,1,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 2) (p 3) (p 4)).mp s234),
            ordered_good (by decide) (by decide) s013,
            ordered_good (by decide) (by decide) s014⟩
  · have s014 : Small (p 0) (p 1) (p 4) := (pair_center_target (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    rcases pair_distinct_targets (show r 2 ≠ r 3 from fun h => (show (r 2).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) (hp 3) with s012 | s013
    · rcases split_corners (show r 0 ≠ 3 from fun h => (show (r 0).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 3 ≠ 3 from fun h => (show (r 3).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 2 ≠ 3 from fun h => (show (r 2).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 0 ≠ r 3 from fun h => (show (r 0).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (show r 0 ≠ r 2 from fun h => (show (r 0).val ≠ (r 2).val by omega) (congrArg Fin.val h)) (show r 3 ≠ r 2 from fun h => (show (r 3).val ≠ (r 2).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 3) (hp 2) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) with s013 | s034 | s024 | s134 | s124 | s234
      · exact ⟨{0,1,4},{0,1,2},{0,1,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s013⟩
      · exact ⟨{0,1,4},{0,1,2},{0,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s034⟩
      · exact ⟨{0,1,4},{0,1,2},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s024⟩
      · exact ⟨{0,1,4},{0,1,2},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s134⟩
      · exact ⟨{0,1,4},{0,1,2},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) s124⟩
      · exact ⟨{0,1,4},{0,1,2},{2,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s012,
          ordered_good (by decide) (by decide) ((small_swap (p 2) (p 3) (p 4)).mp s234)⟩
    · rcases split_corners (show r 0 ≠ 3 from fun h => (show (r 0).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 2 ≠ 3 from fun h => (show (r 2).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 3 ≠ 3 from fun h => (show (r 3).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 0 ≠ r 2 from fun h => (show (r 0).val ≠ (r 2).val by omega) (congrArg Fin.val h)) (show r 0 ≠ r 3 from fun h => (show (r 0).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (show r 2 ≠ r 3 from fun h => (show (r 2).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (hp 0) ((show r 1 = r 0 from Fin.ext (by omega)) ▸ hp 1) (hp 2) (hp 3) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) with s012 | s024 | s034 | s124 | s134 | s234
      · exact ⟨{0,1,4},{0,1,3},{0,1,2},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s012⟩
      · exact ⟨{0,1,4},{0,1,3},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s024⟩
      · exact ⟨{0,1,4},{0,1,3},{0,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s034⟩
      · exact ⟨{0,1,4},{0,1,3},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s124⟩
      · exact ⟨{0,1,4},{0,1,3},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s134⟩
      · exact ⟨{0,1,4},{0,1,3},{2,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s014,
          ordered_good (by decide) (by decide) s013,
          ordered_good (by decide) (by decide) s234⟩
  · have s123 : Small (p 1) (p 2) (p 3) := (same_sector (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) ((show r 3 = r 1 from Fin.ext (by omega)) ▸ hp 3))
    have s124 : Small (p 1) (p 2) (p 4) := (same_sector (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) ((show r 4 = r 1 from Fin.ext (by omega)) ▸ hp 4))
    have s134 : Small (p 1) (p 3) (p 4) := (same_sector (hp 1) ((show r 3 = r 1 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = r 1 from Fin.ext (by omega)) ▸ hp 4))
    exact ⟨{1,2,3},{1,2,4},{1,3,4},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s123,
      ordered_good (by decide) (by decide) s124,
      ordered_good (by decide) (by decide) s134⟩
  · have s123 : Small (p 1) (p 2) (p 3) := (same_sector (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) ((show r 3 = r 1 from Fin.ext (by omega)) ▸ hp 3))
    have s124 : Small (p 1) (p 2) (p 4) := (same_sector (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) ((show r 4 = r 1 from Fin.ext (by omega)) ▸ hp 4))
    have s134 : Small (p 1) (p 3) (p 4) := (same_sector (hp 1) ((show r 3 = r 1 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = r 1 from Fin.ext (by omega)) ▸ hp 4))
    exact ⟨{1,2,3},{1,2,4},{1,3,4},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s123,
      ordered_good (by decide) (by decide) s124,
      ordered_good (by decide) (by decide) s134⟩
  · have s124 : Small (p 1) (p 2) (p 4) := (pair_center_target (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    have s134 : Small (p 1) (p 3) (p 4) := (pair_center_target (hp 1) ((show r 3 = r 1 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    have s123 : Small (p 1) (p 2) (p 3) := (same_sector (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) ((show r 3 = r 1 from Fin.ext (by omega)) ▸ hp 3))
    exact ⟨{1,2,4},{1,3,4},{1,2,3},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s124,
      ordered_good (by decide) (by decide) s134,
      ordered_good (by decide) (by decide) s123⟩
  · have s123 : Small (p 1) (p 2) (p 3) := (same_sector (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) ((show r 3 = r 1 from Fin.ext (by omega)) ▸ hp 3))
    rcases pair_distinct_targets (show r 0 ≠ r 4 from fun h => (show (r 0).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) (hp 0) (hp 4) with s012 | s124
    · rcases pair_distinct_targets (show r 0 ≠ r 4 from fun h => (show (r 0).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 1) ((show r 3 = r 1 from Fin.ext (by omega)) ▸ hp 3) (hp 0) (hp 4) with s013 | s134
      · exact ⟨{1,2,3},{0,1,2},{0,1,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 3)).mp s013)⟩
      · exact ⟨{1,2,3},{0,1,2},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
          ordered_good (by decide) (by decide) s134⟩
    · rcases pair_distinct_targets (show r 0 ≠ r 4 from fun h => (show (r 0).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 1) ((show r 3 = r 1 from Fin.ext (by omega)) ▸ hp 3) (hp 0) (hp 4) with s013 | s134
      · exact ⟨{1,2,3},{1,2,4},{0,1,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 3)).mp s013)⟩
      · exact ⟨{1,2,3},{1,2,4},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) s134⟩
  · have s034 : Small (p 0) (p 3) (p 4) := ((small_cycle (p 0) (p 3) (p 4)).mp (center_pair ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) (hp 0).1))
    have s123 : Small (p 1) (p 2) (p 3) := (pair_center_target (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3))
    have s124 : Small (p 1) (p 2) (p 4) := (pair_center_target (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    exact ⟨{0,3,4},{1,2,3},{1,2,4},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s034,
      ordered_good (by decide) (by decide) s123,
      ordered_good (by decide) (by decide) s124⟩
  · rcases pair_distinct_targets (show r 0 ≠ r 1 from fun h => (show (r 0).val ≠ (r 1).val by omega) (congrArg Fin.val h)) (hp 3) ((show r 4 = r 3 from Fin.ext (by omega)) ▸ hp 4) (hp 0) (hp 1) with s034 | s134
    · rcases pair_distinct_targets (show r 0 ≠ r 3 from fun h => (show (r 0).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) (hp 0) (hp 3) with s012 | s123
      · rcases two_pairs (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) (hp 3) ((show r 4 = r 3 from Fin.ext (by omega)) ▸ hp 4) with s123 | s124 | s134 | s234
        · exact ⟨{0,3,4},{0,1,2},{1,2,3},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
            ordered_good (by decide) (by decide) s123⟩
        · exact ⟨{0,3,4},{0,1,2},{1,2,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
            ordered_good (by decide) (by decide) s124⟩
        · exact ⟨{0,3,4},{0,1,2},{1,3,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
            ordered_good (by decide) (by decide) s134⟩
        · exact ⟨{0,3,4},{0,1,2},{2,3,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
            ordered_good (by decide) (by decide) s234⟩
      · rcases pair_distinct_targets (show r 0 ≠ r 4 from fun h => (show (r 0).val ≠ (r 4).val by omega) (congrArg Fin.val h)) (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) (hp 0) (hp 4) with s012 | s124
        · exact ⟨{0,3,4},{1,2,3},{0,1,2},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) s123,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012)⟩
        · exact ⟨{0,3,4},{1,2,3},{1,2,4},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) s123,
            ordered_good (by decide) (by decide) s124⟩
    · rcases pair_distinct_targets (show r 0 ≠ r 2 from fun h => (show (r 0).val ≠ (r 2).val by omega) (congrArg Fin.val h)) (hp 3) ((show r 4 = r 3 from Fin.ext (by omega)) ▸ hp 4) (hp 0) (hp 2) with s034 | s234
      · rcases pair_distinct_targets (show r 0 ≠ r 3 from fun h => (show (r 0).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) (hp 0) (hp 3) with s012 | s123
        · exact ⟨{1,3,4},{0,3,4},{0,1,2},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 3) (p 4)).mp s134),
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012)⟩
        · exact ⟨{1,3,4},{0,3,4},{1,2,3},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 3) (p 4)).mp s134),
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 3) (p 4)).mp s034),
            ordered_good (by decide) (by decide) s123⟩
      · rcases pair_distinct_targets (show r 0 ≠ r 3 from fun h => (show (r 0).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) (hp 0) (hp 3) with s012 | s123
        · exact ⟨{1,3,4},{2,3,4},{0,1,2},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 3) (p 4)).mp s134),
            ordered_good (by decide) (by decide) ((small_cycle (p 2) (p 3) (p 4)).mp s234),
            ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012)⟩
        · exact ⟨{1,3,4},{2,3,4},{1,2,3},by decide,by decide,by decide,
            ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 3) (p 4)).mp s134),
            ordered_good (by decide) (by decide) ((small_cycle (p 2) (p 3) (p 4)).mp s234),
            ordered_good (by decide) (by decide) s123⟩
  · have s124 : Small (p 1) (p 2) (p 4) := (pair_center_target (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    rcases pair_distinct_targets (show r 0 ≠ r 3 from fun h => (show (r 0).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) (hp 0) (hp 3) with s012 | s123
    · rcases split_corners (show r 1 ≠ 3 from fun h => (show (r 1).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 3 ≠ 3 from fun h => (show (r 3).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 0 ≠ 3 from fun h => (show (r 0).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 1 ≠ r 3 from fun h => (show (r 1).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (show r 1 ≠ r 0 from fun h => (show (r 1).val ≠ (r 0).val by omega) (congrArg Fin.val h)) (show r 3 ≠ r 0 from fun h => (show (r 3).val ≠ (r 0).val by omega) (congrArg Fin.val h)) (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) (hp 3) (hp 0) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) with s123 | s134 | s014 | s234 | s024 | s034
      · exact ⟨{1,2,4},{0,1,2},{1,2,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
          ordered_good (by decide) (by decide) s123⟩
      · exact ⟨{1,2,4},{0,1,2},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
          ordered_good (by decide) (by decide) s134⟩
      · exact ⟨{1,2,4},{0,1,2},{0,1,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
          ordered_good (by decide) (by decide) ((small_swap (p 0) (p 1) (p 4)).mp s014)⟩
      · exact ⟨{1,2,4},{0,1,2},{2,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
          ordered_good (by decide) (by decide) s234⟩
      · exact ⟨{1,2,4},{0,1,2},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
          ordered_good (by decide) (by decide) ((small_swap (p 0) (p 2) (p 4)).mp s024)⟩
      · exact ⟨{1,2,4},{0,1,2},{0,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012),
          ordered_good (by decide) (by decide) ((small_swap (p 0) (p 3) (p 4)).mp s034)⟩
    · rcases split_corners (show r 1 ≠ 3 from fun h => (show (r 1).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 0 ≠ 3 from fun h => (show (r 0).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 3 ≠ 3 from fun h => (show (r 3).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 1 ≠ r 0 from fun h => (show (r 1).val ≠ (r 0).val by omega) (congrArg Fin.val h)) (show r 1 ≠ r 3 from fun h => (show (r 1).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (show r 0 ≠ r 3 from fun h => (show (r 0).val ≠ (r 3).val by omega) (congrArg Fin.val h)) (hp 1) ((show r 2 = r 1 from Fin.ext (by omega)) ▸ hp 2) (hp 0) (hp 3) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) with s012 | s014 | s134 | s024 | s234 | s034
      · exact ⟨{1,2,4},{1,2,3},{0,1,2},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 1) (p 2)).mp s012)⟩
      · exact ⟨{1,2,4},{1,2,3},{0,1,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) ((small_swap (p 0) (p 1) (p 4)).mp s014)⟩
      · exact ⟨{1,2,4},{1,2,3},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) s134⟩
      · exact ⟨{1,2,4},{1,2,3},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) ((small_swap (p 0) (p 2) (p 4)).mp s024)⟩
      · exact ⟨{1,2,4},{1,2,3},{2,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) s234⟩
      · exact ⟨{1,2,4},{1,2,3},{0,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s124,
          ordered_good (by decide) (by decide) s123,
          ordered_good (by decide) (by decide) s034⟩
  · have s023 : Small (p 0) (p 2) (p 3) := ((small_cycle (p 0) (p 2) (p 3)).mp (center_pair ((show r 2 = 3 from Fin.ext (by change (r 2).val = 3; omega)) ▸ hp 2) ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3) (hp 0).1))
    have s123 : Small (p 1) (p 2) (p 3) := ((small_cycle (p 1) (p 2) (p 3)).mp (center_pair ((show r 2 = 3 from Fin.ext (by change (r 2).val = 3; omega)) ▸ hp 2) ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3) (hp 1).1))
    have s234 : Small (p 2) (p 3) (p 4) := (same_sector (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = r 2 from Fin.ext (by omega)) ▸ hp 4))
    exact ⟨{0,2,3},{1,2,3},{2,3,4},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s023,
      ordered_good (by decide) (by decide) s123,
      ordered_good (by decide) (by decide) s234⟩
  · have s234 : Small (p 2) (p 3) (p 4) := (same_sector (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = r 2 from Fin.ext (by omega)) ▸ hp 4))
    rcases pair_distinct_targets (show r 0 ≠ r 1 from fun h => (show (r 0).val ≠ (r 1).val by omega) (congrArg Fin.val h)) (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) (hp 0) (hp 1) with s023 | s123
    · rcases pair_distinct_targets (show r 0 ≠ r 1 from fun h => (show (r 0).val ≠ (r 1).val by omega) (congrArg Fin.val h)) (hp 2) ((show r 4 = r 2 from Fin.ext (by omega)) ▸ hp 4) (hp 0) (hp 1) with s024 | s124
      · exact ⟨{2,3,4},{0,2,3},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 4)).mp s024)⟩
      · exact ⟨{2,3,4},{0,2,3},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 4)).mp s124)⟩
    · rcases pair_distinct_targets (show r 0 ≠ r 1 from fun h => (show (r 0).val ≠ (r 1).val by omega) (congrArg Fin.val h)) (hp 2) ((show r 4 = r 2 from Fin.ext (by omega)) ▸ hp 4) (hp 0) (hp 1) with s024 | s124
      · exact ⟨{2,3,4},{1,2,3},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123),
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 4)).mp s024)⟩
      · exact ⟨{2,3,4},{1,2,3},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 4)).mp s124)⟩
  · have s234 : Small (p 2) (p 3) (p 4) := (pair_center_target (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4))
    rcases pair_distinct_targets (show r 0 ≠ r 1 from fun h => (show (r 0).val ≠ (r 1).val by omega) (congrArg Fin.val h)) (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) (hp 0) (hp 1) with s023 | s123
    · rcases split_corners (show r 2 ≠ 3 from fun h => (show (r 2).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 1 ≠ 3 from fun h => (show (r 1).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 0 ≠ 3 from fun h => (show (r 0).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 2 ≠ r 1 from fun h => (show (r 2).val ≠ (r 1).val by omega) (congrArg Fin.val h)) (show r 2 ≠ r 0 from fun h => (show (r 2).val ≠ (r 0).val by omega) (congrArg Fin.val h)) (show r 1 ≠ r 0 from fun h => (show (r 1).val ≠ (r 0).val by omega) (congrArg Fin.val h)) (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) (hp 1) (hp 0) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) with s123 | s124 | s024 | s134 | s034 | s014
      · exact ⟨{2,3,4},{0,2,3},{1,2,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123)⟩
      · exact ⟨{2,3,4},{0,2,3},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_swap (p 1) (p 2) (p 4)).mp s124)⟩
      · exact ⟨{2,3,4},{0,2,3},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_swap (p 0) (p 2) (p 4)).mp s024)⟩
      · exact ⟨{2,3,4},{0,2,3},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_swap (p 1) (p 3) (p 4)).mp s134)⟩
      · exact ⟨{2,3,4},{0,2,3},{0,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_swap (p 0) (p 3) (p 4)).mp s034)⟩
      · exact ⟨{2,3,4},{0,2,3},{0,1,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023),
          ordered_good (by decide) (by decide) ((small_swap (p 0) (p 1) (p 4)).mp s014)⟩
    · rcases split_corners (show r 2 ≠ 3 from fun h => (show (r 2).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 0 ≠ 3 from fun h => (show (r 0).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 1 ≠ 3 from fun h => (show (r 1).val ≠ 3 by omega) (congrArg Fin.val h)) (show r 2 ≠ r 0 from fun h => (show (r 2).val ≠ (r 0).val by omega) (congrArg Fin.val h)) (show r 2 ≠ r 1 from fun h => (show (r 2).val ≠ (r 1).val by omega) (congrArg Fin.val h)) (show r 0 ≠ r 1 from fun h => (show (r 0).val ≠ (r 1).val by omega) (congrArg Fin.val h)) (hp 2) ((show r 3 = r 2 from Fin.ext (by omega)) ▸ hp 3) (hp 0) (hp 1) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) with s023 | s024 | s124 | s034 | s134 | s014
      · exact ⟨{2,3,4},{1,2,3},{0,2,3},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123),
          ordered_good (by decide) (by decide) ((small_cycle (p 0) (p 2) (p 3)).mp s023)⟩
      · exact ⟨{2,3,4},{1,2,3},{0,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123),
          ordered_good (by decide) (by decide) ((small_swap (p 0) (p 2) (p 4)).mp s024)⟩
      · exact ⟨{2,3,4},{1,2,3},{1,2,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123),
          ordered_good (by decide) (by decide) ((small_swap (p 1) (p 2) (p 4)).mp s124)⟩
      · exact ⟨{2,3,4},{1,2,3},{0,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123),
          ordered_good (by decide) (by decide) ((small_swap (p 0) (p 3) (p 4)).mp s034)⟩
      · exact ⟨{2,3,4},{1,2,3},{1,3,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123),
          ordered_good (by decide) (by decide) ((small_swap (p 1) (p 3) (p 4)).mp s134)⟩
      · exact ⟨{2,3,4},{1,2,3},{0,1,4},by decide,by decide,by decide,
          ordered_good (by decide) (by decide) s234,
          ordered_good (by decide) (by decide) ((small_cycle (p 1) (p 2) (p 3)).mp s123),
          ordered_good (by decide) (by decide) s014⟩
  · have s034 : Small (p 0) (p 3) (p 4) := ((small_cycle (p 0) (p 3) (p 4)).mp (center_pair ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) (hp 0).1))
    have s134 : Small (p 1) (p 3) (p 4) := ((small_cycle (p 1) (p 3) (p 4)).mp (center_pair ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) (hp 1).1))
    have s234 : Small (p 2) (p 3) (p 4) := ((small_cycle (p 2) (p 3) (p 4)).mp (center_pair ((show r 3 = 3 from Fin.ext (by change (r 3).val = 3; omega)) ▸ hp 3) ((show r 4 = 3 from Fin.ext (by change (r 4).val = 3; omega)) ▸ hp 4) (hp 2).1))
    exact ⟨{0,3,4},{1,3,4},{2,3,4},by decide,by decide,by decide,
      ordered_good (by decide) (by decide) s034,
      ordered_good (by decide) (by decide) s134,
      ordered_good (by decide) (by decide) s234⟩

theorem standard_three (p : Fin 5 → Pt) (hp : ∀ i, standard (p i)) :
    Three (fun i j k => Small (p i) (p j) (p k)) := by
  classical
  choose r hr using fun i => sector_cover (hp i)
  let e := Tuple.sort r
  have h := sorted_three (fun i => p (e i)) (fun i => r (e i))
    (Tuple.monotone_sort r) (fun i => hr (e i))
  exact three_map e (fun i j k => (small_swap (p i) (p j) (p k)).mpr)
    (fun i j k => (small_swap_right (p i) (p j) (p k)).mpr) (fun _ _ _ h => h) h

end Kahle
```

### `KahleConjecture.lean`

```lean
import KahleOccupancies

namespace Kahle

/-- The affine map taking the ambient vertices to (0,0), (2,0), (0,2). -/
noncomputable def normalizePoint (a b c x : Pt) : Pt :=
  (2 * det2 a x c / det2 a b c, 2 * det2 a b x / det2 a b c)

theorem normalizePoint_affine (a b c : Pt) :
    Affine (fun x => (normalizePoint a b c x).1) ∧
    Affine (fun x => (normalizePoint a b c x).2) := by
  constructor
  · intro u v p q r
    simp only [normalizePoint,det2,blend]
    ring
  · intro u v p q r
    simp only [normalizePoint,det2,blend]
    ring

theorem normalizePoint_blend {a b c : Pt} (h : det2 a b c ≠ 0) (u v : ℝ) :
    normalizePoint a b c (blend u v a b c) = (2*u,2*v) := by
  have h₁ : det2 a (blend u v a b c) c = u * det2 a b c := by
    simp only [det2,blend]
    ring
  have h₂ : det2 a b (blend u v a b c) = v * det2 a b c := by
    simp only [det2,blend]
    ring
  ext
  · change 2 * det2 a (blend u v a b c) c / det2 a b c = 2*u
    rw [h₁, ← mul_assoc, mul_div_cancel_right₀ _ h]
  · change 2 * det2 a b (blend u v a b c) / det2 a b c = 2*v
    rw [h₂, ← mul_assoc, mul_div_cancel_right₀ _ h]

/-- The normalization takes the given barycentric coefficients at B and C
    to twice those coefficients as Cartesian coordinates. The displayed
    determinant equality also covers degenerate point triples. -/
theorem normalize {A B C : Pt} (hA : triArea A B C = 1) (p : Fin 5 → Pt)
    (hp : ∀ i, InTri A B C (p i)) :
    let q := fun i => normalizePoint A B C (p i)
    (∀ i, standard (q i)) ∧
      ∀ i j k, triArea (p i) (p j) (p k) ≤ 1/4 ↔ Small (q i) (q j) (q k) := by
  classical
  choose a b c ha hb hc habc hx using hp
  have ha' (i : Fin 5) : a i = 1-b i-c i := by linarith [habc i]
  have hbase : |det2 A B C| = 2 := by unfold triArea at hA; linarith
  have hnz : det2 A B C ≠ 0 := by
    intro h
    rw [h,abs_zero] at hbase
    norm_num at hbase
  have hblend (i : Fin 5) : p i = blend (b i) (c i) A B C := by
    rw [hx i,ha' i]
    rfl
  have hq (i : Fin 5) : normalizePoint A B C (p i) = (2*b i,2*c i) := by
    rw [hblend i, normalizePoint_blend hnz]
  dsimp only
  refine ⟨?_, ?_⟩
  · intro i
    rw [hq i]
    change 0 ≤ 2*b i ∧ 0 ≤ 2*c i ∧ 2*b i+2*c i ≤ 2
    exact ⟨by linarith [hb i],by linarith [hc i],by linarith [ha i,habc i]⟩
  · intro i j k
    have hdet : det2 (p i) (p j) (p k) * 4 = det2 A B C *
        det2 (normalizePoint A B C (p i)) (normalizePoint A B C (p j))
          (normalizePoint A B C (p k)) := by
      rw [hq i, hq j, hq k]
      simp only [hblend, det2, blend]
      ring
    have hh := congrArg abs hdet
    simp only [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 4 by norm_num),hbase] at hh
    unfold triArea Small
    constructor <;> intro h <;> linarith

end Kahle

open scoped Classical in
theorem kahle_conj_3_1 (A B C : ℝ × ℝ) (hA : triArea A B C = 1)
    (p : Fin 5 → ℝ × ℝ) (hp : ∀ i, InTri A B C (p i)) :
    3 ≤ ((Finset.univ.powersetCard 3 : Finset (Finset (Fin 5))).filter
          (fun s => ∃ i j k, i < j ∧ j < k ∧ s = {i, j, k} ∧
                     triArea (p i) (p j) (p k) ≤ 1/4)).card := by
  obtain ⟨hq,bridge⟩ := Kahle.normalize hA p hp
  exact Kahle.count_three (Kahle.three_mono (fun i j k => (bridge i j k).mpr)
    (Kahle.standard_three _ hq))

-- A unit triangle containing five distinct points gives nonempty hypotheses.
example :
    ∃ (a b c : ℝ × ℝ) (p : Fin 5 → ℝ × ℝ), triArea a b c = 1 ∧
      Function.Injective p ∧ ∀ i, InTri a b c (p i) := by
  refine ⟨(0,0),(2,0),(0,1),fun i => (i.val / 2,0),?_,?_,?_⟩
  · norm_num [triArea,det2]
  · intro i j h
    have he := congrArg Prod.fst h
    change (i.val : ℝ) / 2 = (j.val : ℝ) / 2 at he
    have hh : (i.val : ℝ) = (j.val : ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast hh)
  · intro i
    have hi : (i.val : ℝ) ≤ 4 := by exact_mod_cast (show i.val ≤ 4 by omega)
    have h0 : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    refine ⟨1 - i.val/4,i.val/4,0,by linarith,by linarith,le_rfl,by ring,?_⟩
    ext <;> simp [smul_eq_mul]; ring

#check kahle_conj_3_1
#print axioms kahle_conj_3_1
```
