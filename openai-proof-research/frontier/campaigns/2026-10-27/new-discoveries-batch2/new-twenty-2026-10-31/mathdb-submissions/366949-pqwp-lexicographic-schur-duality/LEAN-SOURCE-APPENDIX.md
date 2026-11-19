# Exact Lean source appendix for MathDB 366949

Each section holds one complete sealed author module.

## Rule.lean

```lean
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Ring.Rat

namespace FiniteSkew

noncomputable section

abbrev V (ι : Type) := ι →₀ ℚ

def atom {ι : Type} (i : ι) : V ι := Finsupp.single i 1

def out {ι : Type} (r : Option ι) : V ι := (r.map atom).getD 0

structure Rule (ι : Type) where
  e : ι
  product : ι → ι → Option ι
  left_unit : ∀ i, product e i = some i
  right_unit : ∀ i, product i e = some i
  assoc : ∀ i j k,
    (product i j).bind (fun m => product m k) =
      (product j k).bind (product i)

namespace Rule

variable {ι : Type} (R : Rule ι)

def scaled {M : Type} [AddCommMonoid M] [Module ℚ M] (a : M) : ℚ →ₗ[ℚ] M where
  toFun r := r • a
  map_add' r s := add_smul r s a
  map_smul' r s := mul_smul r s a

noncomputable def times : V ι →ₗ[ℚ] V ι →ₗ[ℚ] V ι :=
  Finsupp.lsum ℚ fun i => scaled (Finsupp.lsum ℚ fun j => scaled (out (R.product i j)))

@[simp] theorem times_add_left (x y z : V ι) :
    R.times (x + y) z = R.times x z + R.times y z := by
  rw [map_add]; rfl

@[simp] theorem times_add_right (x y z : V ι) :
    R.times x (y + z) = R.times x y + R.times x z := map_add _ _ _

@[simp] theorem times_zero_left (y : V ι) : R.times 0 y = 0 := by rw [map_zero]; rfl

@[simp] theorem times_zero_right (x : V ι) : R.times x 0 = 0 := map_zero _

@[simp] theorem times_smul_left (r : ℚ) (x y : V ι) :
    R.times (r • x) y = r • R.times x y := by rw [map_smul]; rfl

@[simp] theorem times_smul_right (r : ℚ) (x y : V ι) :
    R.times x (r • y) = r • R.times x y := map_smul _ _ _

@[simp] theorem single_eq_scale (i : ι) (r : ℚ) :
    Finsupp.single i r = r • atom i := by simp [atom, Finsupp.smul_single]

theorem times_atom (i j : ι) : R.times (atom i) (atom j) = out (R.product i j) := by
  simp [times, atom, scaled, -single_eq_scale]

theorem times_left_unit (x : V ι) : R.times (atom R.e) x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i r => simp [times_atom, R.left_unit, out]

theorem times_right_unit (x : V ι) : R.times x (atom R.e) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i r => simp [times_atom, R.right_unit, out]

theorem times_assoc (x y z : V ι) :
    R.times (R.times x y) z = R.times x (R.times y z) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x u hx hu => simp [hx, hu]
  | single i r =>
    simp only [single_eq_scale, times_smul_left]
    congr 1
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y u hy hu => simp [hy, hu]
    | single j s =>
      simp only [single_eq_scale, times_smul_left, times_smul_right]
      congr 1
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add z u hz hu => simp [hz, hu]
      | single k t =>
        simp only [single_eq_scale, times_smul_right]
        congr 1
        have left (a : Option ι) :
            R.times (out a) (atom k) =
              out (a.bind (fun m => R.product m k)) := by
          cases a <;> simp [out, times_atom]
        have right (a : Option ι) :
            R.times (atom i) (out a) = out (a.bind (R.product i)) := by
          cases a <;> simp [out, times_atom]
        rw [times_atom R i j, times_atom R j k, left, right, R.assoc]

@[instance_reducible] noncomputable def ruleRing : Ring (V ι) where
  __ := (inferInstance : AddCommGroup (V ι))
  mul x y := R.times x y
  one := atom R.e
  mul_assoc := R.times_assoc
  one_mul := R.times_left_unit
  mul_one := R.times_right_unit
  left_distrib := R.times_add_right
  right_distrib x y z := R.times_add_left x y z
  zero_mul := R.times_zero_left
  mul_zero := R.times_zero_right
  natCast n := n • atom R.e
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast n := n • atom R.e
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc n := negSucc_zsmul _ _

end Rule

variable {ι : Type}

theorem option_ext {x y : Option ι} (h : ∀ a, x = some a ↔ y = some a) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some a => exact (h a).mpr rfl
  | some a => exact ((h a).mp rfl).symm

theorem bind_some {κ : Type} (x : Option ι) (f : ι → Option κ) (b : κ) :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp

#print axioms Rule.times_assoc
#print axioms Rule.ruleRing
#eval Lean.versionString

end
end FiniteSkew
```

## Model.lean

```lean
import Rule
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases

namespace FiniteSkew

inductive B
  | one | a | b | c | z
  deriving DecidableEq, Repr

def degB : B → ℕ
  | .one => 0
  | .c => 2
  | _ => 1

def mulB : B → B → Option B
  | .one, y => some y
  | x, .one => some x
  | .a, .b => some .c
  | _, _ => none

theorem mulB_assoc (u v w : B) :
    (mulB u v).bind (fun m => mulB m w) = (mulB v w).bind (mulB u) := by
  cases u <;> cases v <;> cases w <;> rfl

def basisRule : Rule B where
  e := .one
  product := mulB
  left_unit _ := rfl
  right_unit i := by cases i <;> rfl
  assoc := mulB_assoc

theorem mulB_degree {i j k : B} (h : mulB i j = some k) :
    degB i + degB j = degB k := by
  cases i <;> cases j <;> cases k <;> (first | rfl | contradiction)

abbrev I := Fin 3
abbrev T := I → B
abbrev P := Equiv.Perm I
abbrev F := V B
abbrev Tensor := V T
abbrev D := V (T × P)

def unitT : T := fun _ => .one

def pack (x : I → Option B) : Option T :=
  match x 0, x 1, x 2 with
  | some x₀, some x₁, some x₂ => some ![x₀,x₁,x₂]
  | _, _, _ => none

theorem pack_some (x : I → Option B) (y : T) :
    pack x = some y ↔ ∀ i, x i = some (y i) := by
  constructor
  · intro h
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      simp [pack, h0, h1, h2] at h
    subst y
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h
    have eq : ![y 0,y 1,y 2] = y := by
      funext i
      fin_cases i <;> rfl
    simp [pack, h 0, h 1, h 2, eq]

def mulT (u v : T) : Option T := pack fun i => mulB (u i) (v i)

theorem mulT_some (u v y : T) :
    mulT u v = some y ↔ ∀ i, mulB (u i) (v i) = some (y i) :=
  pack_some _ _

def tensorRule : Rule T where
  e := unitT
  product := mulT
  left_unit u := (mulT_some _ _ _).mpr fun i => basisRule.left_unit (u i)
  right_unit u := (mulT_some _ _ _).mpr fun i => basisRule.right_unit (u i)
  assoc u v w := by
    apply option_ext
    intro y
    simp only [bind_some, mulT_some]
    constructor
    · rintro ⟨m, hm, hy⟩
      have h (i : I) : ∃ n, mulB (v i) (w i) = some n ∧ mulB (u i) n = some (y i) :=
        (bind_some _ _ _).mp (by rw [← mulB_assoc (u i) (v i) (w i)]; simp [hm i, hy i])
      exact ⟨fun i => (h i).choose, fun i => (h i).choose_spec.1, fun i => (h i).choose_spec.2⟩
    · rintro ⟨n, hn, hy⟩
      have h (i : I) : ∃ m, mulB (u i) (v i) = some m ∧ mulB m (w i) = some (y i) :=
        (bind_some _ _ _).mp (by rw [mulB_assoc (u i) (v i) (w i)]; simp [hn i, hy i])
      exact ⟨fun i => (h i).choose, fun i => (h i).choose_spec.1, fun i => (h i).choose_spec.2⟩

def place (g : P) (u : T) : T := fun i => u (g⁻¹ i)

@[simp] theorem place_one (u : T) : place 1 u = u := rfl

@[simp] theorem place_mul (g h : P) (u : T) : place (g * h) u = place g (place h u) := rfl

@[simp] theorem place_unit (g : P) : place g unitT = unitT := rfl

theorem place_product (g : P) (u v y : T) :
    mulT (place g u) (place g v) = some (place g y) ↔ mulT u v = some y := by
  simp only [mulT_some, place]
  constructor
  · intro h i
    simpa using h (g i)
  · intro h i
    exact h (g⁻¹ i)

def mulD (x y : T × P) : Option (T × P) :=
  (mulT x.1 (place x.2 y.1)).map (fun u => (u, x.2 * y.2))

theorem mulD_some (u v y : T) (g h k : P) :
    mulD (u,g) (v,h) = some (y,k) ↔
      mulT u (place g v) = some y ∧ g * h = k := by
  unfold mulD
  cases mulT u (place g v) <;> simp

def skewRule : Rule (T × P) where
  e := (unitT,1)
  product := mulD
  left_unit := by
    rintro ⟨u,g⟩
    exact (mulD_some _ _ _ _ _ _).mpr ⟨tensorRule.left_unit _, one_mul _⟩
  right_unit := by
    rintro ⟨u,g⟩
    exact (mulD_some _ _ _ _ _ _).mpr ⟨tensorRule.right_unit _, mul_one _⟩
  assoc := by
    rintro ⟨u,g⟩ ⟨v,h⟩ ⟨w,k⟩
    apply option_ext
    rintro ⟨y,p⟩
    simp only [bind_some, Prod.exists, mulD_some]
    constructor
    · rintro ⟨m, q₀, ⟨hm, rfl⟩, hy, hp⟩
      have eq := tensorRule.assoc u (place g v) (place g (place h w))
      change (mulT u (place g v)).bind (fun m => mulT m (place g (place h w))) =
        (mulT (place g v) (place g (place h w))).bind (mulT u) at eq
      have q : ∃ n, mulT (place g v) (place g (place h w)) = some n ∧
          mulT u n = some y := (bind_some _ _ _).mp (by rw [← eq, hm]; simpa only [Option.bind_some, place_mul] using hy)
      obtain ⟨n, hn, hy'⟩ := q
      let n' := place g⁻¹ n
      have he : place g n' = n := by simp [n', ← place_mul]
      exact ⟨n', h*k, ⟨(place_product g _ _ _).mp (he.symm ▸ hn), rfl⟩,
        he.symm ▸ hy', by simpa only [mul_assoc] using hp⟩
    · rintro ⟨n, q₀, ⟨hn, rfl⟩, hy, hp⟩
      have eq := tensorRule.assoc u (place g v) (place g (place h w))
      change (mulT u (place g v)).bind (fun m => mulT m (place g (place h w))) =
        (mulT (place g v) (place g (place h w))).bind (mulT u) at eq
      have q : ∃ m, mulT u (place g v) = some m ∧
          mulT m (place g (place h w)) = some y :=
        (bind_some _ _ _).mp (by rw [eq]; simp [(place_product g _ _ _).mpr hn, hy])
      obtain ⟨m, hm, hy'⟩ := q
      exact ⟨m, g*h, ⟨hm, rfl⟩, hy', by simpa only [mul_assoc] using hp⟩

noncomputable instance : Ring F := basisRule.ruleRing
noncomputable instance : Ring Tensor := tensorRule.ruleRing
noncomputable instance : Ring D := skewRule.ruleRing

theorem basis_mul (i j : B) : (atom i : F) * atom j = out (mulB i j) :=
  basisRule.times_atom _ _

theorem tensor_mul (u v : T) : (atom u : Tensor) * atom v = out (mulT u v) :=
  tensorRule.times_atom _ _

theorem skew_mul (x y : T × P) : (atom x : D) * atom y = out (mulD x y) :=
  skewRule.times_atom _ _

#print axioms mulB_degree
#print axioms tensorRule
#print axioms skewRule
#print axioms skew_mul

end FiniteSkew
```

## Coords.lean

```lean
import Model

namespace FiniteSkew

noncomputable section

def reindex {ι κ : Type} (f : ι → κ) : V ι →ₗ[ℚ] V κ :=
  Finsupp.lsum ℚ (fun i => Rule.scaled (atom (f i)))

@[simp] theorem reindex_atom {ι κ : Type} (f : ι → κ) (i : ι) :
    reindex f (atom i) = atom (f i) := by
  simp [reindex, atom, Rule.scaled, -Rule.single_eq_scale]

@[simp] theorem atom_apply {ι : Type} [DecidableEq ι] (i j : ι) :
    atom i j = if i = j then 1 else 0 := Finsupp.single_apply

def normal (x : Tensor) (g : P) : D := reindex (fun u => (u,g)) x

def action (g : P) (x : Tensor) : Tensor := reindex (place g) x

@[simp] theorem normal_atom (u : T) (g : P) :
    normal (atom u) g = atom (u,g) := reindex_atom _ _

@[simp] theorem action_atom (u : T) (g : P) :
    action g (atom u) = atom (place g u) := reindex_atom _ _

theorem normal_apply (x : Tensor) (g k : P) (u : T) :
    normal x g (u,k) = if g = k then x u else 0 := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [normal]
  | add x y hx hy =>
      change (reindex _ (x+y)) (u,k) = _
      rw [map_add]
      change normal x g (u,k) + normal y g (u,k) = _
      rw [hx, hy]
      split <;> simp
  | single v r =>
      simp only [Rule.single_eq_scale]
      change (reindex _ (r • atom v)) (u,k) = _
      rw [map_smul, reindex_atom]
      simp only [Finsupp.smul_apply, atom_apply, Prod.mk.injEq]
      by_cases e : g = k <;> by_cases e' : v = u <;> simp [e,e']

theorem normal_form (d : D) :
    d = ∑ g : P, normal (Finsupp.lsum ℚ (fun j =>
      Rule.scaled (if j.2 = g then atom j.1 else 0)) d) g := by
  classical
  let col (g : P) : D →ₗ[ℚ] Tensor :=
    Finsupp.lsum ℚ (fun j => Rule.scaled (if j.2 = g then atom j.1 else 0))
  change d = ∑ g : P, normal (col g d) g
  have col_apply (g : P) (u : T) : col g d u = d (u,g) := by
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | single j r =>
        simp only [Rule.single_eq_scale, map_smul, Finsupp.smul_apply, atom_apply]
        have h : col g (atom j) = if j.2 = g then atom j.1 else 0 := by
          simp [col, atom, Rule.scaled, -Rule.single_eq_scale]
        rw [h]
        rcases j with ⟨v,k⟩
        by_cases eq : k = g <;> simp [eq]
  ext j
  rcases j with ⟨u,k⟩
  simp [Finsupp.finsetSum_apply, normal_apply, col_apply]

@[simp] theorem tensor_smul_mul (r : ℚ) (x y : Tensor) :
    (r • x) * y = r • (x * y) := tensorRule.times_smul_left _ _ _

@[simp] theorem tensor_mul_smul (r : ℚ) (x y : Tensor) :
    x * (r • y) = r • (x * y) := tensorRule.times_smul_right _ _ _

@[simp] theorem skew_smul_mul (r : ℚ) (x y : D) :
    (r • x) * y = r • (x * y) := skewRule.times_smul_left _ _ _

@[simp] theorem skew_mul_smul (r : ℚ) (x y : D) :
    x * (r • y) = r • (x * y) := skewRule.times_smul_right _ _ _

theorem normal_mul (x y : Tensor) (g h : P) :
    normal x g * normal y h = normal (x * action g y) (g*h) := by
  induction x using Finsupp.induction_linear with
  | zero => simp [normal]
  | add x z hx hz => simp [normal, map_add, add_mul] at hx hz ⊢; rw [hx, hz]
  | single u r =>
      simp only [Rule.single_eq_scale, normal, map_smul, skew_smul_mul, tensor_smul_mul]
      congr 1
      induction y using Finsupp.induction_linear with
      | zero => simp [action]
      | add y z hy hz => simp [action, map_add, mul_add] at hy hz ⊢; rw [hy, hz]
      | single v s =>
          simp only [Rule.single_eq_scale, action, map_smul, skew_mul_smul,
            tensor_mul_smul, reindex_atom, skew_mul, mulD, tensor_mul]
          cases mulT u (place g v) <;> simp [out]

def rightB (u y : B) : Option B :=
  if u = .one then some y
  else if u = y then some .one
  else if u = .a ∧ y = .c then some .b
  else none

def leftB (y v : B) : Option B :=
  if v = .one then some y
  else if v = y then some .one
  else if v = .b ∧ y = .c then some .a
  else none

theorem rightB_some (u v y : B) : rightB u y = some v ↔ mulB u v = some y := by
  cases u <;> cases v <;> cases y <;> decide

theorem leftB_some (u v y : B) : leftB y v = some u ↔ mulB u v = some y := by
  cases u <;> cases v <;> cases y <;> decide

def rightT (u y : T) : Option T := pack fun i => rightB (u i) (y i)
def leftT (y v : T) : Option T := pack fun i => leftB (y i) (v i)

theorem rightT_some (u v y : T) : rightT u y = some v ↔ mulT u v = some y := by
  simp only [rightT, pack_some, mulT_some, rightB_some]

theorem leftT_some (u v y : T) : leftT y v = some u ↔ mulT u v = some y := by
  simp only [leftT, pack_some, mulT_some, leftB_some]

theorem place_inv (g : P) (v u : T) : place g v = u ↔ v = place g⁻¹ u := by
  constructor <;> intro h
  · rw [← h, ← place_mul, inv_mul_cancel, place_one]
  · rw [h, ← place_mul, mul_inv_cancel, place_one]

theorem mul_left_coeff (u y : T) (g k : P) (x : D) :
    ((atom (u,g) : D) * x) (y,k) =
      ((rightT u y).map (fun v => x (place g⁻¹ v,g⁻¹*k))).getD 0 := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => cases rightT u y <;> simp
  | add x z hx hz =>
      rw [mul_add, Finsupp.add_apply, hx, hz]
      cases rightT u y <;> simp
  | single j r =>
      obtain ⟨v,h⟩ := j
      simp only [Rule.single_eq_scale, skew_mul_smul, Finsupp.smul_apply, skew_mul]
      have test : mulD (u,g) (v,h) = some (y,k) ↔
          ∃ w, rightT u y = some w ∧ v = place g⁻¹ w ∧ h = g⁻¹*k := by
        rw [mulD_some, ← rightT_some]
        constructor
        · rintro ⟨hw, hk⟩
          exact ⟨_, hw, (place_inv _ _ _).mp rfl, (eq_inv_mul_iff_mul_eq).mpr hk⟩
        · rintro ⟨w, hw, hv, hk⟩
          exact ⟨((place_inv _ _ _).mpr hv).symm ▸ hw, (eq_inv_mul_iff_mul_eq).mp hk⟩
      cases e : rightT u y with
      | none =>
          have ne : mulD (u,g) (v,h) ≠ some (y,k) := by simp [test, e, -place_mul]
          cases ee : mulD (u,g) (v,h) with
          | none => simp [out]
          | some l =>
              have hl : l ≠ (y,k) := by simpa [ee] using ne
              simp [out, hl]
      | some w =>
          have eq : mulD (u,g) (v,h) = some (y,k) ↔ (v,h) = (place g⁻¹ w,g⁻¹*k) := by
            simp [test, e]
          cases ee : mulD (u,g) (v,h) with
          | none =>
              have ne := mt eq.mpr (show mulD _ _ ≠ some (y,k) by rw [ee]; intro bad; contradiction)
              simp [out, ne, -Prod.mk.injEq]
          | some l =>
              have hl : l = (y,k) ↔ (v,h) = (place g⁻¹ w,g⁻¹*k) := by simpa [ee] using eq
              simp [out, hl]

theorem mul_right_coeff (v y : T) (h k : P) (x : D) :
    (x * (atom (v,h) : D)) (y,k) =
      ((leftT y (place (k*h⁻¹) v)).map (fun u => x (u,k*h⁻¹))).getD 0 := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => cases leftT y (place (k*h⁻¹) v) <;> simp
  | add x z hx hz =>
      rw [add_mul, Finsupp.add_apply, hx, hz]
      cases leftT y (place (k*h⁻¹) v) <;> simp
  | single j r =>
      obtain ⟨u,g⟩ := j
      simp only [Rule.single_eq_scale, skew_smul_mul, Finsupp.smul_apply, skew_mul]
      have test : mulD (u,g) (v,h) = some (y,k) ↔
          leftT y (place (k*h⁻¹) v) = some u ∧ g = k*h⁻¹ := by
        rw [mulD_some, ← leftT_some, ← eq_mul_inv_iff_mul_eq]
        constructor
        · rintro ⟨hu, rfl⟩
          exact ⟨hu,rfl⟩
        · rintro ⟨hu, rfl⟩
          exact ⟨hu,rfl⟩
      cases e : leftT y (place (k*h⁻¹) v) with
      | none =>
          have ne : mulD (u,g) (v,h) ≠ some (y,k) := by
            intro bad
            have hh := (test.mp bad).1
            rw [e] at hh
            contradiction
          cases ee : mulD (u,g) (v,h) with
          | none => simp [out]
          | some l =>
              have hl : l ≠ (y,k) := by simpa [ee] using ne
              simp [out, hl]
      | some w =>
          have eq : mulD (u,g) (v,h) = some (y,k) ↔ (u,g) = (w,k*h⁻¹) := by
            simp [test, e, -place_mul, eq_comm]
          cases ee : mulD (u,g) (v,h) with
          | none =>
              have ne := mt eq.mpr (show mulD _ _ ≠ some (y,k) by rw [ee]; intro bad; contradiction)
              simp [out, ne, -Prod.mk.injEq]
          | some l =>
              have hl : l = (y,k) ↔ (u,g) = (w,k*h⁻¹) := by simpa [ee] using eq
              simp [out, hl]

#print axioms normal_form
#print axioms normal_mul
#print axioms mul_left_coeff
#print axioms mul_right_coeff

end
end FiniteSkew
```

## NativeK.lean

```lean
import Coords
import Mathlib.Tactic.Abel

namespace FiniteSkew

def s : P := Equiv.swap 0 1
def t : P := Equiv.swap 1 2
def r : P := s*t
def l : P := t*s
def j : P := s*t*s

theorem one_line :
    (![ (1 : P) 0, (1 : P) 1, (1 : P) 2] : I → I) = ![0,1,2] ∧
    (![s 0,s 1,s 2] : I → I) = ![1,0,2] ∧
    (![t 0,t 1,t 2] : I → I) = ![0,2,1] ∧
    (![r 0,r 1,r 2] : I → I) = ![1,2,0] ∧
    (![l 0,l 1,l 2] : I → I) = ![2,0,1] ∧
    (![j 0,j 1,j 2] : I → I) = ![2,1,0] := by decide

def pairT (i k : I) (x y : B) : T := fun n =>
  if n = i then x else if n = k then y else .one

theorem action_pair (g : P) (i k : I) (x y : B) :
    place g (pairT i k x y) = pairT (g i) (g k) x y := by
  funext n
  have key (c : I) : g⁻¹ n = c ↔ n = g c := by
    constructor <;> intro h
    · simpa using congrArg g h
    · simp [h]
  simp only [place, pairT, key]

noncomputable section

def alpha (i k : I) : Tensor := 1 + (atom (pairT i k .a .b) - atom (pairT i k .b .a))

def lexPairs : List (I × I) := [(0,1),(0,2),(1,2)]

def kCoeff (g : P) : Tensor :=
  ((lexPairs.filter fun p => g p.1 < g p.2).map fun p => alpha p.1 p.2).prod

def K : D := ∑ g : P, normal (kCoeff g) g

theorem k_rows :
    kCoeff 1 = alpha 0 1 * alpha 0 2 * alpha 1 2 ∧
    kCoeff s = alpha 0 2 * alpha 1 2 ∧
    kCoeff t = alpha 0 1 * alpha 0 2 ∧
    kCoeff r = alpha 0 1 ∧
    kCoeff l = alpha 1 2 ∧
    kCoeff j = 1 := by
  have e : kCoeff 1 = alpha 0 1 * (alpha 0 2 * (alpha 1 2 * 1)) := rfl
  refine ⟨by rw [e, mul_one, mul_assoc], ?_, ?_, ?_, ?_, rfl⟩
  · change alpha 0 2 * (alpha 1 2 * 1) = _
    rw [mul_one]
  · change alpha 0 1 * (alpha 0 2 * 1) = _
    rw [mul_one]
  · exact mul_one _
  · exact mul_one _

theorem k_coordinate (u : T) (g : P) : K (u,g) = kCoeff g u := by
  classical
  simp [K, Finsupp.finsetSum_apply, normal_apply]

def perms : Finset P := {1,s,t,r,l,j}

theorem perms_univ : perms = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  have h : perms.card = 6 := by decide
  rw [h, Finset.card_univ, Fintype.card_perm]
  decide

theorem sum_perms {M : Type} [AddCommMonoid M] (f : P → M) :
    (∑ g : P, f g) = f 1 + (f s + (f t + (f r + (f l + f j)))) := by
  rw [← perms_univ]
  simp (disch := decide) [perms, Finset.sum_insert]

theorem K_rows :
    K = normal (alpha 0 1 * alpha 0 2 * alpha 1 2) 1 +
      (normal (alpha 0 2 * alpha 1 2) s +
      (normal (alpha 0 1 * alpha 0 2) t +
      (normal (alpha 0 1) r + (normal (alpha 1 2) l + normal 1 j)))) := by
  rw [K, sum_perms, k_rows.1, k_rows.2.1, k_rows.2.2.1, k_rows.2.2.2.1,
    k_rows.2.2.2.2.1, k_rows.2.2.2.2.2]

def up : T := pairT 0 1 .a .b
def um : T := pairT 0 1 .b .a
def vp : T := pairT 0 2 .a .b
def vm : T := pairT 0 2 .b .a
def wp : T := pairT 1 2 .a .b
def wm : T := pairT 1 2 .b .a
def uv : T := ![.c,.b,.a]
def uw : T := ![.b,.c,.a]
def vw : T := ![.b,.a,.c]

def U12 : Tensor := atom up - atom um
def U13 : Tensor := atom vp - atom vm
def U23 : Tensor := atom wp - atom wm

theorem alpha12 : alpha 0 1 = 1+U12 := rfl
theorem alpha13 : alpha 0 2 = 1+U13 := rfl
theorem alpha23 : alpha 1 2 = 1+U23 := rfl

theorem uv_product : U12 * U13 = -atom uv := by
  unfold U12 U13
  simp only [sub_mul, mul_sub, tensor_mul]
  change (0 - 0) - (atom uv - 0) = _
  simp

theorem uw_product : U12 * U23 = atom uw := by
  unfold U12 U23
  simp only [sub_mul, mul_sub, tensor_mul]
  change (0 - 0) - (0 - atom uw) = _
  simp

theorem vw_product : U13 * U23 = -atom vw := by
  unfold U13 U23
  simp only [sub_mul, mul_sub, tensor_mul]
  change (0 - atom vw) - (0 - 0) = _
  simp

theorem uvw_product : (U12 * U13) * U23 = 0 := by
  rw [uv_product]
  unfold U23
  simp only [neg_mul, mul_sub, tensor_mul]
  change -(0 : Tensor) - -0 = 0
  simp

theorem partial_coeff12_13 :
    alpha 0 1 * alpha 0 2 = 1 + U12 + U13 - atom uv := by
  simp only [alpha12, alpha13, add_mul, mul_add, one_mul, mul_one, uv_product]
  abel

theorem partial_coeff13_23 :
    alpha 0 2 * alpha 1 2 = 1 + U13 + U23 - atom vw := by
  simp only [alpha13, alpha23, add_mul, mul_add, one_mul, mul_one, vw_product]
  abel

theorem full_coeff :
    alpha 0 1 * alpha 0 2 * alpha 1 2 =
      1 + U12 + U13 + U23 - atom uv + atom uw - atom vw := by
  have h : (-atom uv : Tensor) * U23 = 0 := by rw [← uv_product, uvw_product]
  simp only [alpha12, alpha13, alpha23, add_mul, mul_add, one_mul, mul_one,
    uw_product, vw_product, uv_product, h]
  abel

@[simp] theorem normal_add (x y : Tensor) (g : P) :
    normal (x+y) g = normal x g + normal y g := map_add _ _ _

@[simp] theorem normal_sub (x y : Tensor) (g : P) :
    normal (x-y) g = normal x g - normal y g := map_sub _ _ _

@[simp] theorem normal_one (g : P) : normal 1 g = atom (unitT,g) := normal_atom _ _

theorem K_atoms :
    K = (atom (unitT,1) + atom (up,1) - atom (um,1) +
          (atom (vp,1) - atom (vm,1)) + (atom (wp,1) - atom (wm,1)) -
          atom (uv,1) + atom (uw,1) - atom (vw,1)) +
        ((atom (unitT,s) + atom (vp,s) - atom (vm,s) +
          (atom (wp,s) - atom (wm,s)) - atom (vw,s)) +
        ((atom (unitT,t) + atom (up,t) - atom (um,t) +
          (atom (vp,t) - atom (vm,t)) - atom (uv,t)) +
        ((atom (unitT,r) + atom (up,r) - atom (um,r)) +
        ((atom (unitT,l) + atom (wp,l) - atom (wm,l)) + atom (unitT,j))))) := by
  rw [K_rows, full_coeff, partial_coeff12_13, partial_coeff13_23, alpha12, alpha23]
  simp only [U12, U13, U23, normal_add, normal_sub, normal_one, normal_atom]
  abel

#print axioms one_line
#print axioms K_rows
#print axioms k_coordinate
#print axioms K_atoms

end
end FiniteSkew
```

## Certificate.lean

```lean
import NativeK

namespace FiniteSkew

noncomputable section

def Z : T := fun _ => .z

def S : D := atom (unitT,s)

def G : D := ∑ g : P, atom (unitT,g)

def K2 : D :=
    (atom (up,1) - atom (um,1) + (atom (vp,1) - atom (vm,1)) +
      (atom (wp,1) - atom (wm,1))) +
    ((atom (vp,s) - atom (vm,s) + (atom (wp,s) - atom (wm,s))) +
    ((atom (up,t) - atom (um,t) + (atom (vp,t) - atom (vm,t))) +
    ((atom (up,r) - atom (um,r)) + (atom (wp,l) - atom (wm,l)))))

def K4 : D := -atom (uv,1) + atom (uw,1) - atom (vw,1) - atom (vw,s) - atom (uv,t)

theorem K_split : K = G + K2 + K4 := by
  rw [K_atoms]
  simp only [G, sum_perms, K2, K4]
  abel

def witness : D :=
  atom (Z,1) + atom (Z,s) + (atom (Z,t) + atom (Z,t)) + (atom (Z,r) + atom (Z,r))

private theorem shift_atom (g : P) (u : T) :
    S * atom (u,g) = atom (place s u,s*g) := by
  rw [S, skew_mul]
  change out ((mulT unitT (place s u)).map (fun v => (v,s*g))) = _
  rw [show mulT unitT (place s u) = some (place s u) from tensorRule.left_unit _]
  rfl

private theorem ss : s*s = 1 := by decide

private theorem sr : s*r = t := by rw [r, ← mul_assoc, ss, one_mul]

private theorem sj : s*j = l := by decide

theorem SG : S * G = G := by
  rw [G, sum_perms]
  simp only [mul_add, shift_atom, place_unit, mul_one, ss, show s*t=r from rfl,
    sr, show s*l=j from (mul_assoc s t s).symm, sj]
  abel

private def abc : T := ![.a,.b,.c]

private theorem shift_up : place s up = um := by decide
private theorem shift_um : place s um = up := by decide
private theorem shift_vp : place s vp = wp := by decide
private theorem shift_vm : place s vm = wm := by decide
private theorem shift_wp : place s wp = vp := by decide
private theorem shift_wm : place s wm = vm := by decide
private theorem shift_uv : place s uv = uw := by decide
private theorem shift_uw : place s uw = uv := by decide
private theorem shift_vw : place s vw = abc := by decide

private theorem right_up : rightT up up = some unitT :=
  (rightT_some _ _ _).mpr (tensorRule.right_unit up)

private theorem right_um : rightT um up = none := rfl
private theorem right_vp : rightT vp up = none := rfl
private theorem right_vm : rightT vm up = none := rfl
private theorem right_wp : rightT wp up = none := rfl
private theorem right_wm : rightT wm up = none := rfl
private theorem right_uv : rightT uv up = none := rfl
private theorem right_uw : rightT uw up = none := rfl
private theorem right_vw : rightT vw up = none := rfl
private theorem right_abc : rightT abc up = none := rfl

theorem K2_at (h : D) (k : P) :
    (K2*h) (up,k) = h (unitT,k) + h (unitT,t⁻¹*k) + h (unitT,r⁻¹*k) := by
  simp only [K2, add_mul, sub_mul, Finsupp.add_apply, Finsupp.sub_apply,
    mul_left_coeff, right_up, right_um, right_vp, right_vm, right_wp, right_wm,
    Option.map_some, Option.getD_some, Option.map_none, Option.getD_none,
    place_unit, inv_one, one_mul, sub_zero, zero_add, add_zero]
  abel

theorem SK2_at (h : D) (k : P) :
    ((S*K2)*h) (up,k) = -(h (unitT,s⁻¹*k) + h (unitT,r⁻¹*k) + h (unitT,t⁻¹*k)) := by
  simp only [K2, mul_add, mul_sub, shift_atom, shift_up, shift_um, shift_vp, shift_vm, shift_wp,
    shift_wm, mul_one, ss, show s*t=r from rfl, sr, show s*l=j from (mul_assoc s t s).symm,
    add_mul, sub_mul, Finsupp.add_apply, Finsupp.sub_apply,
    mul_left_coeff, right_up, right_um, right_vp, right_vm, right_wp, right_wm,
    Option.map_some, Option.getD_some, Option.map_none, Option.getD_none,
    place_unit]
  abel

theorem K4_at (h : D) (k : P) : (K4*h) (up,k) = 0 := by
  simp [K4, add_mul, sub_mul, mul_left_coeff, right_uv, right_uw, right_vw]

theorem SK4_at (h : D) (k : P) : ((S*K4)*h) (up,k) = 0 := by
  simp [K4, mul_add, mul_sub, shift_atom, shift_uv, shift_uw, shift_vw,
    add_mul, sub_mul, mul_left_coeff, right_uv, right_uw, right_abc]

private theorem mulB_z_left (v y : B) :
    mulB .z v = some y ↔ v = .one ∧ y = .z := by
  cases v <;> cases y <;> decide

private theorem right_Z (u : T) :
    rightT Z u = if u = Z then some unitT else none := by
  apply option_ext
  intro v
  simp only [rightT_some, mulT_some, Z, mulB_z_left]
  by_cases h : u = Z
  · rw [ite_eq_left h]
    subst u
    simp only [Z, and_true, Option.some.injEq]
    exact ⟨fun e => (funext e).symm, fun e i => (congrFun e i).symm⟩
  · rw [ite_eq_right h]
    constructor
    · intro e
      exact False.elim (h (funext fun i => (e i).2))
    · intro e
      contradiction

theorem witness_at (h : D) (u : T) (k : P) :
    (witness*h) (u,k) = if u = Z then
      h (unitT,k) + h (unitT,s⁻¹*k) +
        (h (unitT,t⁻¹*k) + h (unitT,t⁻¹*k)) +
        (h (unitT,r⁻¹*k) + h (unitT,r⁻¹*k))
      else 0 := by
  classical
  by_cases e : u = Z <;>
    simp [witness, add_mul, mul_left_coeff, right_Z, e]

theorem extraction (h : D) (k : P) :
    (((1-S)*K)*h) (up,k) = (witness*h) (Z,k) := by
  rw [K_split]
  simp only [sub_mul, one_mul, mul_add, add_mul, SG, Finsupp.sub_apply, Finsupp.add_apply,
    K2_at, SK2_at, K4_at, SK4_at, witness_at]
  simp
  abel

private def active (v : T) : Prop := ∃ i : I, v i ≠ .one ∧ v i ≠ .z

private theorem active_place (v : T) (g : P) (h : active v) : active (place g v) := by
  rcases h with ⟨i, hi⟩
  exact ⟨g i, by simpa [place] using hi⟩

private theorem mulB_z_right (u v : B) (h : mulB u v = some .z) :
    v = .one ∨ v = .z := by
  cases u <;> cases v <;> (first | contradiction | simp)

private theorem left_Z_active (v : T) (h : active v) : leftT Z v = none := by
  cases e : leftT Z v with
  | none => rfl
  | some u =>
      obtain ⟨i,hi₁,hi₂⟩ := h
      have q := (mulT_some _ _ _).mp ((leftT_some _ _ _).mp e) i
      exact False.elim ((mulB_z_right _ _ q).elim hi₁ hi₂)

private theorem left_Z_unit : leftT Z unitT = some Z :=
  (leftT_some _ _ _).mpr (tensorRule.right_unit Z)

private theorem d_radical_at (d : D) (v : T) (g k : P) (hv : active v) :
    (d * atom (v,g)) (Z,k) = 0 := by
  rw [mul_right_coeff, left_Z_active _ (active_place _ _ hv)]
  rfl

private theorem active_up : active up := ⟨0, by decide, by decide⟩
private theorem active_um : active um := ⟨0, by decide, by decide⟩
private theorem active_vp : active vp := ⟨0, by decide, by decide⟩
private theorem active_vm : active vm := ⟨0, by decide, by decide⟩
private theorem active_wp : active wp := ⟨1, by decide, by decide⟩
private theorem active_wm : active wm := ⟨1, by decide, by decide⟩
private theorem active_uv : active uv := ⟨0, by decide, by decide⟩
private theorem active_uw : active uw := ⟨0, by decide, by decide⟩
private theorem active_vw : active vw := ⟨0, by decide, by decide⟩

theorem dG_at (d : D) (k : P) :
    (d*G) (Z,k) = ∑ g : P, d (Z,g) := by
  simp only [G, Finset.mul_sum, Finsupp.finsetSum_apply, mul_right_coeff,
    place_unit, left_Z_unit, Option.map_some, Option.getD_some]
  let e : P ≃ P :=
    { toFun := fun g => k*g⁻¹
      invFun := fun g => g⁻¹*k
      left_inv := by intro g; simp [mul_inv_rev, mul_assoc]
      right_inv := by intro g; simp [mul_inv_rev, ← mul_assoc k] }
  exact e.sum_comp (fun g => d (Z,g))

theorem constant_Z_row (d : D) (k : P) :
    (d*K) (Z,k) = ∑ g : P, d (Z,g) := by
  simp only [K_split, mul_add, Finsupp.add_apply, dG_at, K2, K4, mul_sub, mul_neg,
    Finsupp.sub_apply, Finsupp.neg_apply,
    d_radical_at d _ _ _ active_up, d_radical_at d _ _ _ active_um,
    d_radical_at d _ _ _ active_vp, d_radical_at d _ _ _ active_vm,
    d_radical_at d _ _ _ active_wp, d_radical_at d _ _ _ active_wm,
    d_radical_at d _ _ _ active_uv, d_radical_at d _ _ _ active_uw,
    d_radical_at d _ _ _ active_vw, sub_zero, add_zero, neg_zero]

theorem witness_not_constant : witness (Z,1) ≠ witness (Z,j) := by
  have s1 : s ≠ 1 := by decide
  have t1 : t ≠ 1 := by decide
  have r1 : r ≠ 1 := by decide
  have ej : (1:P) ≠ j := by decide
  have sj' : s ≠ j := by decide
  have tj : t ≠ j := by decide
  have rj : r ≠ j := by decide
  simp [witness, Finsupp.add_apply, s1, t1, r1, ej, sj', tj, rj]

theorem witness_annihilates (h : D) (hh : K*h = 0) : witness*h = 0 := by
  ext q
  rcases q with ⟨u,k⟩
  by_cases he : u = Z
  · subst u
    rw [← extraction, mul_assoc, hh, mul_zero]
    rfl
  · rw [witness_at, ite_eq_right he]
    rfl

theorem witness_not_mem : ¬ ∃ d : D, d*K = witness := by
  rintro ⟨d, hd⟩
  apply witness_not_constant
  rw [← hd, constant_Z_row, constant_Z_row]

theorem finite_strict :
    ∃ b : D, (∀ h : D, K*h = 0 → b*h = 0) ∧ ¬ ∃ d : D, d*K = b :=
  ⟨witness, witness_annihilates, witness_not_mem⟩

#print axioms K_split
#print axioms extraction
#print axioms constant_Z_row
#print axioms witness_not_constant
#print axioms finite_strict

end
end FiniteSkew
```

## TensorBinding.lean

```lean
import Certificate
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

namespace FiniteSkew

open scoped TensorProduct

noncomputable section

instance : Algebra ℚ F :=
  Algebra.ofModule basisRule.times_smul_left basisRule.times_smul_right

instance : Algebra ℚ Tensor :=
  Algebra.ofModule tensor_smul_mul tensor_mul_smul

instance : Algebra ℚ D :=
  Algebra.ofModule skew_smul_mul skew_mul_smul

abbrev AbstractCube := (F ⊗[ℚ] F) ⊗[ℚ] F

def triples : ((B × B) × B) ≃ T where
  toFun x := ![x.1.1,x.1.2,x.2]
  invFun u := ((u 0,u 1),u 2)
  left_inv _ := rfl
  right_inv u := by
    funext i
    fin_cases i <;> rfl

def fBasis : Module.Basis B ℚ F := Finsupp.basisSingleOne

def cubeBasis : Module.Basis T ℚ AbstractCube :=
  ((fBasis.tensorProduct fBasis).tensorProduct fBasis).reindex triples

def tensorSemantics : Tensor ≃ₗ[ℚ] AbstractCube := cubeBasis.repr.symm

@[simp] theorem semantics_atom (u : T) :
    tensorSemantics (atom u) = ((atom (u 0) : F) ⊗ₜ[ℚ] atom (u 1)) ⊗ₜ[ℚ] atom (u 2) := by
  change cubeBasis.repr.symm (Finsupp.single u 1) = _
  rw [← cubeBasis.repr_self u, LinearEquiv.symm_apply_apply]
  simp only [cubeBasis, Module.Basis.reindex_apply, Module.Basis.tensorProduct_apply']
  rfl

@[simp] theorem semantics_one : tensorSemantics 1 = 1 := by
  change tensorSemantics (atom unitT) = 1
  rw [semantics_atom, Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def]
  rfl

theorem semantics_mul (x y : Tensor) :
    tensorSemantics (x*y) = tensorSemantics x * tensorSemantics y := by
  induction x using Finsupp.induction_linear with
  | zero =>
      simp only [zero_mul, map_zero]
      exact (zero_mul (tensorSemantics y)).symm
  | add x u hx hu =>
      simp only [add_mul, map_add, hx, hu]
      exact ((inferInstance : Semiring AbstractCube).right_distrib _ _ _).symm
  | single u c =>
      simp only [Rule.single_eq_scale, map_smul, smul_mul_assoc]
      congr 1
      induction y using Finsupp.induction_linear with
      | zero =>
          simp only [mul_zero, map_zero]
          exact (mul_zero (tensorSemantics (atom u))).symm
      | add y v hy hv =>
          simp only [mul_add, map_add, hy, hv]
          exact ((inferInstance : Semiring AbstractCube).left_distrib _ _ _).symm
      | single v d =>
          simp only [Rule.single_eq_scale, map_smul, mul_smul_comm]
          congr 1
          rw [tensor_mul, semantics_atom, semantics_atom]
          simp only [Algebra.TensorProduct.tmul_mul_tmul, basis_mul, mulT, pack]
          cases mulB (u 0) (v 0) <;>
            cases mulB (u 1) (v 1) <;>
            cases mulB (u 2) (v 2) <;>
            simp [out]

def tensorAlgebraEquiv : Tensor ≃ₐ[ℚ] AbstractCube :=
  { tensorSemantics with
    map_mul' := semantics_mul
    commutes' := by intro c; simp [Algebra.algebraMap_eq_smul_one] }

@[simp] theorem action_identity (x : Tensor) : action 1 x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp [action]
  | add x y hx hy =>
      simp only [action, map_add] at hx hy ⊢
      rw [hx, hy]
  | single u c => simp [Rule.single_eq_scale, action]

theorem action_comp (g h : P) (x : Tensor) : action (g*h) x = action g (action h x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp [action]
  | add x y hx hy =>
      simp only [action, map_add] at hx hy ⊢
      rw [hx, hy]
  | single u c => simp [Rule.single_eq_scale, action]

@[simp] theorem action_unit (g : P) : action g (1 : Tensor) = 1 :=
  action_atom unitT g

theorem action_product (g : P) (x y : Tensor) : action g (x*y) = action g x * action g y := by
  induction x using Finsupp.induction_linear with
  | zero => simp [action]
  | add x u hx hu =>
      simp only [action, map_add, add_mul] at hx hu ⊢
      rw [hx, hu]
  | single u c =>
      simp only [Rule.single_eq_scale, action, map_smul, tensor_smul_mul]
      congr 1
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y v hy hv =>
          simp only [map_add, mul_add] at hy hv ⊢
          rw [hy, hv]
      | single v d =>
          simp only [Rule.single_eq_scale, map_smul, tensor_mul_smul, reindex_atom, tensor_mul]
          have e : mulT (place g u) (place g v) = (mulT u v).map (place g) := by
            apply option_ext
            intro w
            have hw : place g (place g⁻¹ w) = w := (place_inv _ _ _).mpr rfl
            conv_lhs => rw [← hw]
            rw [place_product]
            cases e : mulT u v with
            | none => simp
            | some p => simp [place_inv]
          rw [e]
          cases mulT u v <;> simp [out]

theorem lexPairs_exact (i k : I) : (i,k) ∈ lexPairs ↔ i < k := by
  fin_cases i <;> fin_cases k <;> decide

theorem noninversion_exact (g : P) (i k : I) (h : i < k) :
    g i < g k ↔ ¬ g k < g i := by
  constructor
  · exact not_lt_of_gt
  · intro hn
    exact lt_of_le_of_ne (le_of_not_gt hn) (fun eq => h.ne (g.injective eq))

theorem alpha_is_literal (i k : I) :
    tensorAlgebraEquiv (alpha i k) =
      1 + (tensorAlgebraEquiv (atom (pairT i k .a .b)) -
        tensorAlgebraEquiv (atom (pairT i k .b .a))) := by
  simp only [alpha, map_add, map_one, map_sub]

#print axioms lexPairs_exact
#print axioms noninversion_exact
#print axioms alpha_is_literal
#print axioms tensorAlgebraEquiv
#print axioms action_comp
#print axioms action_product

end
end FiniteSkew
```

## FiniteCore.lean

```lean
import TensorBinding

namespace FiniteSkew

noncomputable section

def tensorDegree (u : T) : ℕ := ∑ i : I, degB (u i)

theorem tensorDegree_place (g : P) (u : T) : tensorDegree (place g u) = tensorDegree u :=
  Equiv.sum_comp (g⁻¹ : P) (fun i => degB (u i))

theorem tensorDegree_product {u v w : T} (h : mulT u v = some w) :
    tensorDegree u + tensorDegree v = tensorDegree w := by
  simp only [tensorDegree, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => mulB_degree ((mulT_some _ _ _).mp h i)

theorem skewDegree_product {u v w : T} {g h k : P}
    (e : mulD (u,g) (v,h) = some (w,k)) :
    tensorDegree u + tensorDegree v = tensorDegree w := by
  rw [← tensorDegree_place g v]
  exact tensorDegree_product ((mulD_some _ _ _ _ _ _).mp e).1

def Homogeneous (n : ℕ) (d : D) : Prop :=
  ∀ u : T, ∀ g : P, tensorDegree u ≠ n → d (u,g) = 0

private theorem homAtom {n : ℕ} (u : T) (g : P) (h : tensorDegree u = n) :
    Homogeneous n (atom (u,g)) := by
  intro v k hv
  have ne : u ≠ v := fun e => hv (e ▸ h)
  simp [atom_apply, ne]

private theorem homAdd {n : ℕ} {d e : D}
    (hd : Homogeneous n d) (he : Homogeneous n e) : Homogeneous n (d+e) := by
  intro u g h
  simp [hd u g h, he u g h]

private theorem homSub {n : ℕ} {d e : D}
    (hd : Homogeneous n d) (he : Homogeneous n e) : Homogeneous n (d-e) := by
  intro u g h
  simp [hd u g h, he u g h]

private theorem homNeg {n : ℕ} {d : D} (hd : Homogeneous n d) : Homogeneous n (-d) := by
  intro u g h
  simp [hd u g h]

theorem K_homogeneous_components :
    Homogeneous 0 G ∧ Homogeneous 2 K2 ∧ Homogeneous 4 K4 := by
  constructor
  · intro u g h
    simp only [G, Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun k _ => homAtom unitT k (by decide) u g h
  · constructor
    · unfold K2
      repeat' first | apply homAdd | apply homSub | apply homAtom
      all_goals decide
    · unfold K4
      repeat' first | apply homAdd | apply homSub | apply homNeg | apply homAtom
      all_goals decide

def abstractKRow (g : P) : AbstractCube :=
  ((lexPairs.filter (fun p => g p.1 < g p.2)).map
      (fun p => tensorAlgebraEquiv (alpha p.1 p.2))).prod

theorem nativeK_binding (g : P) :
    tensorAlgebraEquiv (kCoeff g) = abstractKRow g := by
  simp only [kCoeff, abstractKRow]
  generalize lexPairs.filter (fun p => g p.1 < g p.2) = pairs
  induction pairs with
  | nil => exact map_one tensorAlgebraEquiv
  | cons p pairs ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, ih]

theorem leftIdeal_in_doubleAnnihilator (d : D) (h : D) (hh : K*h = 0) :
    (d*K)*h = 0 := by rw [mul_assoc, hh, mul_zero]

#print axioms skewDegree_product
#print axioms K_homogeneous_components
#print axioms nativeK_binding
#print axioms finite_strict

end
end FiniteSkew
```

## PolyModel.lean

```lean
import FiniteCore
import Mathlib.LinearAlgebra.Finsupp.Defs

namespace PolySkew

open FiniteSkew
noncomputable section

abbrev Exp := I → ℕ
abbrev Tag := Exp × (T × P)
abbrev H := V Tag

def move (g : P) (m : Exp) : Exp := fun i => m (g⁻¹ i)

@[simp] theorem move_one (m : Exp) : move 1 m = m := rfl
@[simp] theorem move_zero (g : P) : move g 0 = 0 := rfl
@[simp] theorem move_add (g : P) (m n : Exp) :
    move g (m+n) = move g m + move g n := rfl
theorem move_mul (g h : P) (m : Exp) :
    move (g*h) m = move g (move h m) := rfl

theorem move_eq_zero (g : P) (m : Exp) : move g m = 0 ↔ m = 0 := by
  constructor
  · intro h
    simpa [← move_mul] using congrArg (move g⁻¹) h
  · rintro rfl
    exact move_zero g

def polyProduct (x y : Tag) : Option Tag :=
  (mulD x.2 y.2).map (fun d => (move y.2.2⁻¹ x.1 + y.1, d))

theorem polyProduct_some (m n p : Exp) (d e f : T × P) :
    polyProduct (m,d) (n,e) = some (p,f) ↔
      mulD d e = some f ∧ move e.2⁻¹ m + n = p := by
  unfold polyProduct
  cases mulD d e <;> simp [and_comm]

theorem mulD_perm {d e f : T × P} (he : mulD d e = some f) :
    d.2 * e.2 = f.2 :=
  ((mulD_some d.1 e.1 f.1 d.2 e.2 f.2).mp he).2

theorem ordered_exponents (e f : P) (m n p : Exp) :
    move f⁻¹ (move e⁻¹ m + n) + p =
      move (e*f)⁻¹ m + (move f⁻¹ n + p) := by
  rw [move_add, ← move_mul, mul_inv_rev, add_assoc]

def polyRule : Rule Tag where
  e := (0,skewRule.e)
  product := polyProduct
  left_unit := by
    rintro ⟨m,d⟩
    exact (polyProduct_some _ _ _ _ _ _).mpr ⟨skewRule.left_unit _, by simp⟩
  right_unit := by
    rintro ⟨m,d⟩
    exact (polyProduct_some _ _ _ _ _ _).mpr ⟨skewRule.right_unit _, by simp [skewRule]⟩
  assoc := by
    rintro ⟨m,d⟩ ⟨n,e⟩ ⟨p,f⟩
    apply option_ext
    rintro ⟨q,k⟩
    simp only [bind_some]
    constructor
    · rintro ⟨⟨a,j⟩,hj,hk⟩
      obtain ⟨hjD,rfl⟩ := (polyProduct_some _ _ _ _ _ _).mp hj
      obtain ⟨hk,hq⟩ := (polyProduct_some _ _ _ _ _ _).mp hk
      have he : (mulD e f).bind (mulD d) = some k := by
        change (skewRule.product e f).bind (skewRule.product d) = some k
        rw [← skewRule.assoc]
        exact (bind_some _ _ _).mpr ⟨j,hjD,hk⟩
      obtain ⟨l,hl,hlk⟩ := (bind_some _ _ _).mp he
      refine ⟨(move f.2⁻¹ n+p,l),(polyProduct_some _ _ _ _ _ _).mpr ⟨hl,rfl⟩,
        (polyProduct_some _ _ _ _ _ _).mpr ⟨hlk,?_⟩⟩
      rw [← mulD_perm hl, ← ordered_exponents]
      exact hq
    · rintro ⟨⟨a,l⟩,hl,hk⟩
      obtain ⟨hlD,rfl⟩ := (polyProduct_some _ _ _ _ _ _).mp hl
      obtain ⟨hk,hq⟩ := (polyProduct_some _ _ _ _ _ _).mp hk
      have he : (mulD d e).bind (fun j => mulD j f) = some k := by
        change (skewRule.product d e).bind (fun j => skewRule.product j f) = some k
        rw [skewRule.assoc]
        exact (bind_some _ _ _).mpr ⟨l,hlD,hk⟩
      obtain ⟨j,hj,hjk⟩ := (bind_some _ _ _).mp he
      refine ⟨(move e.2⁻¹ m+n,j),(polyProduct_some _ _ _ _ _ _).mpr ⟨hj,rfl⟩,
        (polyProduct_some _ _ _ _ _ _).mpr ⟨hjk,?_⟩⟩
      rw [ordered_exponents, mulD_perm hlD]
      exact hq

noncomputable instance : Ring H := polyRule.ruleRing

theorem poly_atom_mul (x y : Tag) : (atom x : H) * atom y = out (polyProduct x y) :=
  polyRule.times_atom x y

@[simp] theorem one_H : (1 : H) = atom (0,skewRule.e) := rfl
@[simp] theorem poly_smul_mul (r : ℚ) (x y : H) : (r • x) * y = r • (x*y) :=
  polyRule.times_smul_left r x y
@[simp] theorem poly_mul_smul (r : ℚ) (x y : H) : x * (r • y) = r • (x*y) :=
  polyRule.times_smul_right r x y

def rightNormal : H ≃ₗ[ℚ] Exp →₀ D := Finsupp.curryLinearEquiv ℚ

def rightCoeff (h : H) (m : Exp) : D := rightNormal h m

def rightTerm (m : Exp) : D →ₗ[ℚ] H :=
  rightNormal.symm.toLinearMap.comp (Finsupp.lsingle m)

theorem rightCoeff_apply (h : H) (m : Exp) (d : T × P) :
    rightCoeff h m d = h (m,d) := rfl

theorem rightCoeff_ext {h k : H} (he : ∀ m, rightCoeff h m = rightCoeff k m) : h = k :=
  rightNormal.injective (Finsupp.ext he)

@[simp] theorem rightNormal_term (m : Exp) (d : D) :
    rightNormal (rightTerm m d) = Finsupp.single m d :=
  rightNormal.apply_symm_apply _

@[simp] theorem rightCoeff_term (m n : Exp) (d : D) :
    rightCoeff (rightTerm m d) n = if m = n then d else 0 := by
  classical
  simp [rightCoeff, Finsupp.single_apply]

@[simp] theorem rightTerm_atom (m : Exp) (d : T × P) :
    rightTerm m (atom d) = atom (m,d) := by
  classical
  ext ⟨n,e⟩
  rw [← rightCoeff_apply, rightCoeff_term]
  by_cases h : m = n <;> simp [h, atom_apply]

theorem right_decomposition (h : H) :
    h = (rightNormal h).sum fun m d => rightTerm m d := by
  classical
  apply rightNormal.injective
  rw [Finsupp.sum, map_sum]
  simp only [rightNormal_term]
  exact (Finsupp.sum_single (rightNormal h)).symm

#print axioms polyRule
#print axioms right_decomposition

end
end PolySkew
```

## PolyLift.lean

```lean
import PolyModel

namespace PolySkew

open FiniteSkew
noncomputable section

@[simp] theorem rightCoeff_zero (m : Exp) : rightCoeff 0 m = 0 := by
  simp [rightCoeff]

@[simp] theorem rightCoeff_add (h k : H) (m : Exp) :
    rightCoeff (h+k) m = rightCoeff h m + rightCoeff k m := by
  simp [rightCoeff]

@[simp] theorem rightCoeff_smul (r : ℚ) (h : H) (m : Exp) :
    rightCoeff (r • h) m = r • rightCoeff h m := by
  simp [rightCoeff]

theorem term_mul_atoms (m n : Exp) (d e : T × P) :
    rightTerm m (atom d) * rightTerm n (atom e) =
      rightTerm (move e.2⁻¹ m + n) ((atom d : D) * atom e) := by
  rw [rightTerm_atom, rightTerm_atom, poly_atom_mul, skew_mul]
  unfold polyProduct
  cases mulD d e <;> simp [out]

theorem const_left_mul (d e : D) (m : Exp) :
    rightTerm 0 d * rightTerm m e = rightTerm m (d*e) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d f hd hf => simp [add_mul, hd, hf]
  | single u r =>
    simp only [Rule.single_eq_scale, map_smul, poly_smul_mul, skew_smul_mul]
    congr 1
    induction e using Finsupp.induction_linear with
    | zero => simp
    | add e f he hf => simp only [map_add, mul_add, he, hf]
    | single v q =>
      simp only [Rule.single_eq_scale, map_smul, poly_mul_smul, skew_mul_smul]
      rw [term_mul_atoms, move_zero, zero_add]

theorem left_coeff (d : D) (h : H) (m : Exp) :
    rightCoeff (rightTerm 0 d * h) m = d * rightCoeff h m := by
  classical
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h k hh hk => simp [mul_add, hh, hk]
  | single q r =>
    rcases q with ⟨n,e⟩
    simp only [Rule.single_eq_scale, poly_mul_smul, rightCoeff_smul, skew_mul_smul]
    rw [← rightTerm_atom, const_left_mul, rightCoeff_term, rightCoeff_term]
    split <;> simp

def iota : D →+* H where
  toFun d := rightTerm 0 d
  map_zero' := map_zero _
  map_one' := by
    change rightTerm 0 (atom skewRule.e) = _
    simp
  map_add' := map_add _
  map_mul' d e := (const_left_mul d e 0).symm

theorem add_exp_eq_zero (m n : Exp) : m+n=0 ↔ m=0 ∧ n=0 := by
  constructor
  · intro h
    have hh (i : I) : m i = 0 ∧ n i = 0 :=
      Nat.add_eq_zero_iff.mp (congrFun h i)
    exact ⟨funext fun i => (hh i).1,funext fun i => (hh i).2⟩
  · rintro ⟨rfl,rfl⟩
    simp

theorem zero_coeff_mul (h k : H) :
    rightCoeff (h*k) 0 = rightCoeff h 0 * rightCoeff k 0 := by
  classical
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h f hh hf => simp [add_mul, hh, hf]
  | single u r =>
    rcases u with ⟨m,d⟩
    simp only [Rule.single_eq_scale, poly_smul_mul, rightCoeff_smul, skew_smul_mul]
    congr 1
    induction k using Finsupp.induction_linear with
    | zero => simp
    | add k f hk hf => simp [mul_add, hk, hf]
    | single v q =>
      rcases v with ⟨n,e⟩
      simp only [Rule.single_eq_scale, poly_mul_smul, rightCoeff_smul, skew_mul_smul]
      rw [← rightTerm_atom m d, ← rightTerm_atom n e, term_mul_atoms]
      simp only [rightCoeff_term, add_exp_eq_zero, move_eq_zero]
      by_cases hm : m=0 <;> by_cases hn : n=0 <;> simp [hm,hn]

def augment : H →+* D where
  toFun h := rightCoeff h 0
  map_zero' := rightCoeff_zero _
  map_one' := by
    change rightCoeff (atom (0,skewRule.e)) 0 = atom skewRule.e
    exact (congrArg (fun z => rightCoeff z 0) (rightTerm_atom 0 skewRule.e)).symm.trans
      (by rw [rightCoeff_term]; split <;> first | rfl | contradiction)
  map_add' h k := rightCoeff_add h k _
  map_mul' := zero_coeff_mul

@[simp] theorem augment_iota (d : D) : augment (iota d) = d := by
  change rightCoeff (rightTerm 0 d) 0 = d
  simp

theorem coefficientwise_iota (d : D) (h : H) (m : Exp) :
    rightCoeff (iota d*h) m = d*rightCoeff h m := left_coeff d h m

theorem polynomial_annihilator (d : D) (h : H) :
    iota d*h = 0 ↔ ∀ m, d * rightCoeff h m = 0 := by
  constructor
  · intro hzero m
    rw [← coefficientwise_iota, hzero, rightCoeff_zero]
  · intro hz
    apply rightCoeff_ext
    intro m
    rw [coefficientwise_iota, hz, rightCoeff_zero]

theorem polynomial_strict :
    ∃ b : H, (∀ h : H, iota K*h=0 → b*h=0) ∧ ¬ ∃ d : H, d*iota K=b := by
  obtain ⟨b, hb, hn⟩ := finite_strict
  refine ⟨iota b,?_,?_⟩
  · intro h hh
    exact (polynomial_annihilator b h).mpr fun m =>
      hb _ ((polynomial_annihilator K h).mp hh m)
  · rintro ⟨d,hd⟩
    exact hn ⟨augment d, by simpa using congrArg augment hd⟩

#print axioms coefficientwise_iota
#print axioms augment_iota
#print axioms polynomial_strict

end
end PolySkew
```

## PolyBinding.lean

```lean
import PolyLift
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Module

namespace PolySkew

open FiniteSkew
noncomputable section
set_option maxHeartbeats 1000000

instance : Algebra ℚ H :=
  Algebra.ofModule poly_smul_mul poly_mul_smul

abbrev A := AddMonoidAlgebra Tensor Exp

def mono (m : Exp) : Tensor →ₗ[ℚ] A :=
  (AddMonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap.comp (Finsupp.lsingle m)

theorem mono_apply (m : Exp) (d : Tensor) :
    mono m d = AddMonoidAlgebra.single m d := rfl

def leftTerm (g : P) : A →ₗ[ℚ] H :=
  (Finsupp.lsum ℚ (fun m =>
    (rightTerm (move g⁻¹ m)).comp (reindex (fun u => (u,g))))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

def placePoly (g : P) : A →ₗ[ℚ] A :=
  (Finsupp.lsum ℚ (fun m => (mono (move g m)).comp (reindex (place g)))).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem leftTerm_mono (g : P) (m : Exp) (d : Tensor) :
    leftTerm g (mono m d) = rightTerm (move g⁻¹ m) (normal d g) := by
  change (Finsupp.lsum ℚ _) (Finsupp.single m d) = _
  simp [normal]

@[simp] theorem placePoly_mono (g : P) (m : Exp) (d : Tensor) :
    placePoly g (mono m d) = mono (move g m) (action g d) := by
  change (Finsupp.lsum ℚ _) (Finsupp.single m d) = _
  simp [action]

@[simp] theorem mono_mul (m n : Exp) (d e : Tensor) :
    mono m d * mono n e = mono (m+n) (d*e) :=
  AddMonoidAlgebra.single_mul_single _ _ _ _

@[simp] theorem poly_one : (1 : A) = mono 0 1 := rfl

theorem moved_left_exponents (g h : P) (m n : Exp) :
    move h⁻¹ (move g⁻¹ m) + move h⁻¹ n =
      move (g*h)⁻¹ (m + move g n) := by
  rw [move_add, mul_inv_rev, move_mul h⁻¹ g⁻¹ m, move_mul h⁻¹ g⁻¹ (move g n), ← move_mul g⁻¹ g, inv_mul_cancel, move_one]

theorem leftTerm_mono_mul (g h : P) (m n : Exp) (d e : Tensor) :
    leftTerm g (mono m d) * leftTerm h (mono n e) =
      leftTerm (g*h) (mono (m + move g n) (d * action g e)) := by
  simp only [leftTerm_mono]
  induction d using Finsupp.induction_linear with
  | zero => simp [normal]
  | add d f hd hf => simp [normal, map_add, add_mul] at hd hf ⊢; rw [hd,hf]
  | single u r =>
    simp only [Rule.single_eq_scale, normal, map_smul, poly_smul_mul, tensor_smul_mul]
    congr 1
    induction e using Finsupp.induction_linear with
    | zero => simp [action]
    | add e f he hf => simp [action, map_add, mul_add] at he hf ⊢; rw [he,hf]
    | single v q =>
      simp only [Rule.single_eq_scale, action, map_smul, poly_mul_smul,
        tensor_mul_smul, reindex_atom, term_mul_atoms, skew_mul, mulD, tensor_mul,
        moved_left_exponents]
      cases mulT u (place g v) <;> simp [out]

theorem skew_polynomial_mul (g h : P) (f a : A) :
    leftTerm g f * leftTerm h a = leftTerm (g*h) (f * placePoly g a) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f b hf hb => simp only [map_add, add_mul, hf, hb]
  | single m d =>
    change leftTerm g (mono m d) * leftTerm h a = _
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, mul_add, ha, hb]
    | single n e =>
      change leftTerm g (mono m d) * leftTerm h (mono n e) =
        leftTerm (g*h) (mono m d * placePoly g (mono n e))
      rw [placePoly_mono, mono_mul, leftTerm_mono_mul]

def leftCoeff (g : P) : H →ₗ[ℚ] A :=
  Finsupp.lsum ℚ fun (m,(u,h)) =>
    Rule.scaled (if h = g then mono (move g m) (atom u) else 0)

@[simp] theorem leftCoeff_atom (g h : P) (m : Exp) (u : T) :
    leftCoeff g (atom (m,(u,h))) =
      if h = g then mono (move g m) (atom u) else 0 := by
  simp [leftCoeff, atom, Rule.scaled, -Rule.single_eq_scale]

theorem leftCoeff_term (g h : P) (f : A) :
    leftCoeff g (leftTerm h f) = if h = g then f else 0 := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f a hf ha => simp only [map_add, hf, ha]; split <;> simp
  | single m d =>
    change leftCoeff g (leftTerm h (mono m d)) = _
    rw [leftTerm_mono]
    induction d using Finsupp.induction_linear with
    | zero => simp [normal]
    | add d e hd he =>
      simp only [normal, map_add] at hd he ⊢
      rw [hd,he]
      split <;> simp
    | single u r =>
      simp only [Rule.single_eq_scale, normal, reindex_atom, map_smul, rightTerm_atom,
        leftCoeff_atom]
      split
      · rename_i eq
        subst g
        rw [← move_mul, mul_inv_cancel, move_one]
        exact (map_smul (mono m) r (atom u)).symm
      · simp

theorem left_normal (x : H) : x = ∑ g : P, leftTerm g (leftCoeff g x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) hx hy
  | single q r =>
    rcases q with ⟨m,u,g⟩
    simp only [Rule.single_eq_scale, map_smul, ← Finset.smul_sum]
    congr 1
    simp [leftCoeff_atom, apply_ite (leftTerm _), leftTerm_mono, ← move_mul]

theorem leftTerm_one (g : P) : leftTerm g (1 : A) = atom (0,(unitT,g)) := by
  rw [poly_one, leftTerm_mono, move_zero]
  change rightTerm 0 (normal (atom unitT) g) = _
  rw [normal_atom, rightTerm_atom]

theorem placePoly_one (a : A) : placePoly 1 a = a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single m d =>
    change placePoly 1 (mono m d) = _
    rw [placePoly_mono, move_one, action_identity]
    rfl

def includeA : A →+* H where
  toFun := leftTerm 1
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := leftTerm_one 1
  map_mul' a b := by
    simpa only [placePoly_one, mul_one] using (skew_polynomial_mul 1 1 a b).symm

def sigmaUnit : P →* H where
  toFun g := leftTerm g 1
  map_one' := includeA.map_one
  map_mul' g h := by
    have oneAct : placePoly g 1 = 1 := by simp [action_unit]
    simpa only [oneAct, mul_one] using (skew_polynomial_mul g h 1 1).symm

@[simp] theorem term_factorization (g : P) (a : A) :
    includeA a * sigmaUnit g = leftTerm g a := by
  change leftTerm 1 a * leftTerm g 1 = _
  rw [skew_polynomial_mul, placePoly_one, mul_one, one_mul]

theorem wreath (g : P) (a : A) :
    sigmaUnit g * includeA a = includeA (placePoly g a) * sigmaUnit g := by
  change leftTerm g 1 * leftTerm 1 a = _
  rw [skew_polynomial_mul, one_mul, mul_one, term_factorization]

theorem includeA_mono (m : Exp) (a : Tensor) :
    includeA (mono m a) = rightTerm m (normal a 1) := by
  change leftTerm 1 (mono m a) = _
  rw [leftTerm_mono, inv_one, move_one]

theorem right_variables (m : Exp) (d : D) :
    iota d * includeA (mono m 1) = rightTerm m d := by
  rw [includeA_mono]
  change rightTerm 0 d * rightTerm m (normal 1 1) = _
  rw [const_left_mul]
  have he : normal 1 1 = (1 : D) := normal_atom unitT 1
  rw [he, mul_one]

#print axioms skew_polynomial_mul
#print axioms left_normal
#print axioms wreath
#print axioms right_variables

end
end PolySkew
```

## PresentationBase.lean

```lean
import PolyBinding

namespace PolySkew
open FiniteSkew
noncomputable section

theorem placePoly_comp (g h : P) (f : A) :
    placePoly (g*h) f = placePoly g (placePoly h f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f a hf ha => simp only [map_add, hf, ha]
  | single m d =>
    change placePoly (g*h) (mono m d) = placePoly g (placePoly h (mono m d))
    simp only [placePoly_mono, move_mul, action_comp]

theorem leftTerm_injective (g : P) : Function.Injective (leftTerm g) := by
  intro a b he
  simpa [leftCoeff_term] using congrArg (leftCoeff g) he

section Universal
variable {R : Type*} [Ring R]
variable (c : A →+* R) (v : P →* R)
variable (cross : ∀ g a, v g * c a = c (placePoly g a) * v g)

def liftAdd : H →+ R :=
  ∑ g : P, ((AddMonoidHom.mulRight (v g)).comp c.toAddMonoidHom).comp
    (leftCoeff g).toAddMonoidHom

theorem liftAdd_apply (x : H) :
    liftAdd c v x = ∑ g : P, c (leftCoeff g x) * v g := by
  change (AddMonoidHom.eval x) (liftAdd c v) = _
  rw [liftAdd, map_sum]
  rfl

@[simp] theorem liftAdd_term (g : P) (a : A) :
    liftAdd c v (leftTerm g a) = c a * v g := by
  classical
  rw [liftAdd_apply]
  simp [leftCoeff_term, apply_ite c, ite_mul]

include cross in
theorem liftAdd_mul_terms (g h : P) (a b : A) :
    liftAdd c v (leftTerm g a * leftTerm h b) =
      liftAdd c v (leftTerm g a) * liftAdd c v (leftTerm h b) := by
  rw [skew_polynomial_mul, liftAdd_term, liftAdd_term, liftAdd_term, map_mul, map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (c (placePoly g b)), ← cross, mul_assoc]

include cross in
theorem liftAdd_mul (x y : H) :
    liftAdd c v (x*y) = liftAdd c v x * liftAdd c v y := by
  conv_lhs => rw [left_normal x, left_normal y]
  conv_rhs => rw [left_normal x, left_normal y]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum,
    liftAdd_mul_terms c v cross]

def lift : H →+* R where
  __ := liftAdd c v
  map_one' := by
    change liftAdd c v 1 = 1
    rw [← includeA.map_one]
    change liftAdd c v (leftTerm 1 1) = 1
    rw [liftAdd_term, map_one, map_one, mul_one]
  map_mul' := liftAdd_mul c v cross

@[simp] theorem lift_include (a : A) : lift c v cross (includeA a) = c a := by
  change liftAdd c v (leftTerm 1 a) = _
  rw [liftAdd_term, map_one, mul_one]

@[simp] theorem lift_sigma (g : P) : lift c v cross (sigmaUnit g) = v g := by
  change liftAdd c v (leftTerm g 1) = _
  rw [liftAdd_term, map_one, one_mul]

theorem hom_unique (f k : H →+* R)
    (hc : ∀ a, f (includeA a) = k (includeA a))
    (hv : ∀ g, f (sigmaUnit g) = k (sigmaUnit g)) : f = k := by
  ext x
  rw [left_normal x, map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← term_factorization, map_mul, map_mul, hc, hv]

end Universal

theorem placePoly_mul (g : P) (a b : A) :
    placePoly g (a*b) = placePoly g a * placePoly g b := by
  apply leftTerm_injective g
  simp only [← term_factorization]
  rw [← wreath, map_mul, ← mul_assoc, wreath, mul_assoc, wreath, ← mul_assoc,
    ← map_mul]

def placePolyAut (g : P) : A ≃+* A where
  toFun := placePoly g
  invFun := placePoly g⁻¹
  left_inv f := by
    rw [← placePoly_comp, inv_mul_cancel, placePoly_one]
  right_inv f := by
    rw [← placePoly_comp, mul_inv_cancel, placePoly_one]
  map_add' := map_add _
  map_mul' := placePoly_mul g

#print axioms lift
#print axioms hom_unique
#print axioms placePolyAut

end
end PolySkew
```

## NativePresentation.lean

```lean
import PresentationBase

namespace PolySkew
open FiniteSkew
noncomputable section

theorem sixPerms (g : P) : g = 1 ∨ g = s ∨ g = t ∨ g = r ∨ g = l ∨ g = j :=
  (by decide : ∀ g : P, g = 1 ∨ g = s ∨ g = t ∨ g = r ∨ g = l ∨ g = j) g

private theorem id_s : (1 : P) * s = s := by decide
private theorem id_t : (1 : P) * t = t := by decide
private theorem s_s : (s : P) * s = 1 := by decide
private theorem s_t : (s : P) * t = r := by decide
private theorem t_s : (t : P) * s = l := by decide
private theorem t_t : (t : P) * t = 1 := by decide
private theorem r_s : (r : P) * s = j := by decide
private theorem r_t : (r : P) * t = s := by decide
private theorem l_s : (l : P) * s = t := by decide
private theorem l_t : (l : P) * t = j := by decide
private theorem j_s : (j : P) * s = r := by decide
private theorem j_t : (j : P) * t = l := by decide

private theorem j_braid : t*s*t = j := by decide

section Words
variable {R : Type*} [Ring R]
variable (u v : R)

def word (g : P) : R :=
  if g = 1 then 1 else if g = s then u else if g = t then v
  else if g = r then u*v else if g = l then v*u else u*v*u

@[simp] theorem word_id : word u v 1 = 1 := rfl
@[simp] theorem word_s : word u v s = u := rfl
@[simp] theorem word_t : word u v t = v := rfl
@[simp] theorem word_r : word u v r = u*v := rfl
@[simp] theorem word_l : word u v l = v*u := rfl
@[simp] theorem word_j : word u v j = u*v*u := rfl

variable (usq : u*u=1) (vsq : v*v=1) (braid : u*v*u=v*u*v)

include usq in
theorem word_mul_s (g : P) : word u v (g*s) = word u v g * u := by
  rcases sixPerms g with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [s_s, t_s, r_s, l_s, j_s,
    word_id, word_s, word_t, word_r, word_l, word_j, one_mul,
    mul_assoc, usq, mul_one]

include vsq braid in
theorem word_mul_t (g : P) : word u v (g*t) = word u v g * v := by
  rcases sixPerms g with rfl|rfl|rfl|rfl|rfl|rfl
  · simp
  · rfl
  · simp only [t_t, word_id, word_t, vsq]
  · simp only [r_t, word_s, word_r, mul_assoc, vsq, mul_one]
  · rw [l_t, word_j, word_l, braid]
  · rw [j_t, word_l, word_j, braid, mul_assoc (v*u), vsq, mul_one]

include usq vsq braid in
theorem word_mul (g h : P) : word u v (g*h) = word u v g * word u v h := by
  rcases sixPerms h with rfl|rfl|rfl|rfl|rfl|rfl
  · simp
  · exact word_mul_s u v usq g
  · exact word_mul_t u v vsq braid g
  · rw [word_r, r, ← mul_assoc g s t, word_mul_t u v vsq braid, word_mul_s u v usq, mul_assoc]
  · rw [word_l, l, ← mul_assoc g t s, word_mul_s u v usq, word_mul_t u v vsq braid, mul_assoc]
  · change word u v (g*(s*t*s)) = word u v g * (u*v*u)
    rw [← mul_assoc g (s*t) s, ← mul_assoc g s t, word_mul_s u v usq,
      word_mul_t u v vsq braid, word_mul_s u v usq]
    simp only [mul_assoc]

def wordHom : P →* R where
  toFun := word u v
  map_one' := word_id u v
  map_mul' := word_mul u v usq vsq braid

variable (c : A →+* R)
variable (cs : ∀ a, u*c a = c (placePoly s a)*u)
variable (ct : ∀ a, v*c a = c (placePoly t a)*v)

include cs ct in
theorem adjacent_covariance (g : P) (a : A) :
    word u v g*c a = c (placePoly g a)*word u v g := by
  rcases sixPerms g with rfl|rfl|rfl|rfl|rfl|rfl
  · simp [placePoly_one]
  · exact cs a
  · exact ct a
  · rw [word_r, r, placePoly_comp, mul_assoc, ct, ← mul_assoc, cs, mul_assoc]
  · rw [word_l, l, placePoly_comp, mul_assoc, cs, ← mul_assoc, ct, mul_assoc]
  · rw [word_j, j, placePoly_comp, placePoly_comp, mul_assoc (u*v), cs,
      ← mul_assoc, mul_assoc u v, ct, ← mul_assoc, cs]
    simp only [mul_assoc]

def nativeLift : H →+* R :=
  lift c (wordHom u v usq vsq braid) (adjacent_covariance u v c cs ct)

theorem nativeLift_relations :
    (∀ a, nativeLift u v usq vsq braid c cs ct (includeA a) = c a) ∧
    nativeLift u v usq vsq braid c cs ct (sigmaUnit s) = u ∧
    nativeLift u v usq vsq braid c cs ct (sigmaUnit t) = v := by
  simp [nativeLift, wordHom]

theorem adjacent_hom_unique (f k : H →+* R)
    (hc : ∀ a, f (includeA a) = k (includeA a))
    (hs : f (sigmaUnit s) = k (sigmaUnit s))
    (ht : f (sigmaUnit t) = k (sigmaUnit t)) : f = k := by
  apply hom_unique f k hc
  intro g
  rcases sixPerms g with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [r, l, j, map_one, map_mul, hs, ht]

end Words

theorem nativeRelations :
    sigmaUnit s * sigmaUnit s = 1 ∧
    sigmaUnit t * sigmaUnit t = 1 ∧
    sigmaUnit s * sigmaUnit t * sigmaUnit s = sigmaUnit t * sigmaUnit s * sigmaUnit t ∧
    ∀ a, (sigmaUnit s * includeA a = includeA (placePoly s a) * sigmaUnit s) ∧
         (sigmaUnit t * includeA a = includeA (placePoly t a) * sigmaUnit t) := by
  refine ⟨?_, ?_, ?_, fun a => ⟨wreath s a, wreath t a⟩⟩
  · rw [← map_mul, s_s, map_one]
  · rw [← map_mul, t_t, map_one]
  · simp only [← map_mul, j_braid]
    rfl

theorem nativePresentation {R : Type*} [Ring R]
    (c : A →+* R) (u v : R)
    (usq : u*u=1) (vsq : v*v=1) (braid : u*v*u=v*u*v)
    (cs : ∀ a, u*c a = c (placePoly s a)*u)
    (ct : ∀ a, v*c a = c (placePoly t a)*v) :
    ∃! f : H →+* R,
      (∀ a, f (includeA a) = c a) ∧ f (sigmaUnit s) = u ∧ f (sigmaUnit t) = v := by
  let f := nativeLift u v usq vsq braid c cs ct
  have hf := nativeLift_relations u v usq vsq braid c cs ct
  refine ⟨f,hf,?_⟩
  intro k hk
  exact adjacent_hom_unique k f (fun a => (hk.1 a).trans (hf.1 a).symm)
    (hk.2.1.trans hf.2.1.symm) (hk.2.2.trans hf.2.2.symm)

#print axioms nativeRelations
#print axioms nativePresentation

end
end PolySkew
```

## EndComparison.lean

```lean
import NativePresentation
import Mathlib.Algebra.Module.Opposite
import Mathlib.LinearAlgebra.Pi

namespace PolySkew
open FiniteSkew
noncomputable section
set_option maxHeartbeats 1000000

inductive Comp3
  | full | firstTwo | lastTwo | unit
  deriving DecidableEq

instance : Fintype Comp3 where
  elems := {.full,.firstTwo,.lastTwo,.unit}
  complete c := by cases c <;> simp

def Comp3.parts : Comp3 → List ℕ
  | .full => [3]
  | .firstTwo => [2,1]
  | .lastTwo => [1,2]
  | .unit => [1,1,1]

theorem compositions_exact (xs : List ℕ) (hs : xs.sum = 3)
    (hp : ∀ x ∈ xs, 0 < x) : ∃! c : Comp3, c.parts = xs := by
  have inj : Function.Injective Comp3.parts := by
    intro i j h
    cases i <;> cases j <;> first | rfl | contradiction
  suffices he : ∃ c : Comp3, c.parts = xs by
    obtain ⟨c,hc⟩ := he
    exact ⟨c,hc,fun d hd => inj (hd.trans hc.symm)⟩
  rcases xs with _|⟨a,_|⟨b,_|⟨c,_|⟨d,tail⟩⟩⟩⟩
  · simp at hs
  · simp at hs
    exact ⟨.full, by simp [Comp3.parts,hs]⟩
  · have ha := hp a (by simp)
    have hb := hp b (by simp)
    simp at hs
    by_cases h : a = 2
    · exact ⟨.firstTwo, by have : b=1 := by omega
                           simp [Comp3.parts,h,this]⟩
    · have h1 : a=1 := by omega
      have h2 : b=2 := by omega
      exact ⟨.lastTwo,by simp [Comp3.parts,h1,h2]⟩
  · have ha := hp a (by simp)
    have hb := hp b (by simp)
    have hc := hp c (by simp)
    simp at hs
    have h1 : a=1 := by omega
    have h2 : b=1 := by omega
    have h3 : c=1 := by omega
    exact ⟨.unit,by simp [Comp3.parts,h1,h2,h3]⟩
  · have ha := hp a (by simp)
    have hb := hp b (by simp)
    have hc := hp c (by simp)
    have hd := hp d (by simp)
    simp only [List.sum_cons] at hs
    omega

theorem compositions_valid (c : Comp3) :
    c.parts.sum = 3 ∧ ∀ x ∈ c.parts, 0 < x := by
  cases c <;> simp [Comp3.parts]

def parabolic : Comp3 → Finset P
  | .full => Finset.univ
  | .firstTwo => {1,s}
  | .lastTwo => {1,t}
  | .unit => {1}

def orderedPairs : Comp3 → List (I × I)
  | .full => lexPairs
  | .firstTwo => [(0,1)]
  | .lastTwo => [(1,2)]
  | .unit => []

def compK (c : Comp3) : H :=
  ∑ g ∈ parabolic c, includeA (mono 0 (((orderedPairs c).filter
      (fun p => g p.1 < g p.2)).map (fun p => alpha p.1 p.2)).prod) * sigmaUnit g

theorem k_full : compK .full = iota K := by
  change (∑ g : P, includeA (mono 0 (kCoeff g)) * sigmaUnit g) = iota K
  rw [K,map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [term_factorization,leftTerm_mono,move_zero]
  rfl

@[simp] theorem k_unit : compK .unit = 1 := by
  simp only [compK, parabolic, Finset.sum_singleton, orderedPairs, List.filter_nil,
    List.map_nil, List.prod_nil, ← poly_one, map_one, one_mul]

section RightModules
variable {R : Type*} [Ring R]

def mulLeft (a : R) : R →ₗ[Rᵐᵒᵖ] R where
  toFun h := a*h
  map_add' := mul_add _
  map_smul' r h := by
    change a*(h*r.unop) = (a*h)*r.unop
    exact (mul_assoc _ _ _).symm

def principal (a : R) : Submodule Rᵐᵒᵖ R := (mulLeft a).range

theorem principal_spec (a : R) (z : principal a) : ∃ h, a*h=(z:R) := z.property

def mkPrincipal (a h : R) : principal a := ⟨a*h, ⟨h,rfl⟩⟩

def rightGen (a : R) : principal a := mkPrincipal a 1

@[simp] theorem rightGen_val (a : R) : (rightGen a : R) = a := mul_one a

theorem compatible (a b : R) (hb : ∀ h, a*h=0 → b*h=0)
    (x y : R) (he : a*x=a*y) : b*x=b*y := by
  have hz : a*(x-y)=0 := by rw [mul_sub,he,sub_self]
  exact sub_eq_zero.mp (by simpa only [mul_sub] using hb _ hz)

def descFun (a b : R) (z : principal a) : R := b*(principal_spec a z).choose

theorem descFun_spec (a b : R) (hb : ∀ h, a*h=0 → b*h=0)
    (z : principal a) (h : R) (he : a*h = (z:R)) : descFun a b z = b*h :=
  compatible a b hb _ _ ((principal_spec a z).choose_spec.trans he.symm)

def desc (a b : R) (hb : ∀ h, a*h=0 → b*h=0) : principal a →ₗ[Rᵐᵒᵖ] R where
  toFun := descFun a b
  map_add' x y := by
    obtain ⟨u,hu⟩ := principal_spec a x
    obtain ⟨v,hv⟩ := principal_spec a y
    rw [descFun_spec a b hb x u hu, descFun_spec a b hb y v hv,
      descFun_spec a b hb (x+y) (u+v) (by rw [mul_add,hu,hv]; rfl), mul_add]
  map_smul' r x := by
    obtain ⟨u,hu⟩ := principal_spec a x
    rw [descFun_spec a b hb x u hu,
      descFun_spec a b hb (r • x) (u*r.unop) (by
        change a*(u*r.unop) = (x:R)*r.unop
        rw [← mul_assoc,hu])]
    exact (mul_assoc _ _ _).symm

@[simp] theorem desc_eval (a b : R) (hb : ∀ h, a*h=0 → b*h=0) (h : R) :
    desc a b hb (mkPrincipal a h) = b*h :=
  descFun_spec a b hb _ h rfl

@[simp] theorem desc_generator (a b : R) (hb : ∀ h, a*h=0 → b*h=0) :
    desc a b hb (rightGen a) = b := (desc_eval a b hb 1).trans (mul_one b)

abbrev Block (a b : R) := {z : R // (∃ h, a*h=z) ∧ (∃ h, h*b=z)}

theorem block_ann {a b : R} (q : Block a b) (h : R) (hh : b*h=0) :
    (q:R)*h=0 := by
  obtain ⟨w,hw⟩ := q.property.2
  rw [← hw,mul_assoc,hh,mul_zero]

def blockHom {a b : R} (q : Block a b) : principal b →ₗ[Rᵐᵒᵖ] principal a :=
  (desc b (q:R) (block_ann q)).codRestrict (principal a) fun z => by
    obtain ⟨u,hu⟩ := principal_spec b z
    obtain ⟨w,hw⟩ := q.property.1
    change ∃ h, a*h=descFun b (q:R) z
    rw [descFun_spec b (q:R) (block_ann q) z u hu, ← hw]
    exact ⟨w*u,(mul_assoc _ _ _).symm⟩

@[simp] theorem block_eval {a b : R} (q : Block a b) (h : R) :
    (blockHom q (mkPrincipal b h) : R) = (q:R)*h := desc_eval b q (block_ann q) h

@[simp] theorem block_generator {a b : R} (q : Block a b) :
    (blockHom q (rightGen b) : R) = (q:R) := desc_generator b q (block_ann q)

theorem block_action_as_left_mul {a b : R} (q : Block a b)
    (w : R) (hw : w*b=(q:R)) (z : principal b) :
    (blockHom q z : R) = w*(z:R) := by
  obtain ⟨h,hh⟩ := principal_spec b z
  have hz : z=mkPrincipal b h := Subtype.ext hh.symm
  rw [hz,block_eval,← hw,mul_assoc]
  rfl

def blockProduct {a b c : R} (q : Block a b) (r : Block b c) : Block a c :=
  ⟨(blockHom q ⟨(r:R), r.property.1⟩ : R),
    (blockHom q ⟨(r:R),r.property.1⟩).property, by
      obtain ⟨w,hw⟩ := q.property.2
      obtain ⟨v,hv⟩ := r.property.2
      rw [block_action_as_left_mul q w hw]
      exact ⟨w*v,by rw [mul_assoc,hv]⟩⟩

theorem prescribed_product {a b c : R} (q : Block a b) (r : Block b c)
    (x y : R) (hx : x*b=(q:R)) (hy : b*y=(r:R)) :
    (blockProduct q r : R) = x*b*y := by
  change (blockHom q ⟨(r:R),r.property.1⟩ : R) = _
  rw [block_action_as_left_mul q x hx]
  change x*(r:R)=_
  rw [← hy,mul_assoc]

end RightModules

abbrev C := ∀ i : Comp3, principal (compK i)
abbrev Intersection := ∀ i j : Comp3, Block (compK i) (compK j)

def comparison (q : Intersection) : C →ₗ[Hᵐᵒᵖ] C :=
  LinearMap.pi fun i => ∑ j, (blockHom (q i j)).comp (LinearMap.proj j)

theorem comparison_apply (q : Intersection) (x : C) (i : Comp3) :
    comparison q x i = ∑ j, blockHom (q i j) (x j) := by
  simp [comparison, LinearMap.sum_apply]

def injectSummand (i : Comp3) : principal (compK i) →ₗ[Hᵐᵒᵖ] C :=
  LinearMap.single Hᵐᵒᵖ (fun i => ↥(principal (compK i))) i

def unitRange : H →ₗ[Hᵐᵒᵖ] principal (compK .unit) :=
  LinearMap.id.codRestrict _ fun h => ⟨h, by change compK .unit * h = h; rw [k_unit, one_mul]⟩

theorem comparison_probe (q : Intersection) :
    (comparison q (injectSummand .full (rightGen (compK .full))) .unit : H) =
      (q .unit .full : H) := by
  rw [comparison_apply]
  classical
  rw [Finset.sum_eq_single Comp3.full]
  · simp [injectSummand]
  · intro j _ hj
    simp [injectSummand, hj]
  · simp

def missingEnd (b : H) (hb : ∀ h : H, compK .full * h = 0 → b*h=0) :
    C →ₗ[Hᵐᵒᵖ] C :=
  let pr : C →ₗ[Hᵐᵒᵖ] principal (compK .full) :=
    LinearMap.proj (R := Hᵐᵒᵖ) (φ := fun i => ↥(principal (compK i))) .full
  let f : principal (compK .full) →ₗ[Hᵐᵒᵖ] H := desc (compK .full) b hb
  let g : C →ₗ[Hᵐᵒᵖ] H := f.comp pr
  let g' : C →ₗ[Hᵐᵒᵖ] principal (compK .unit) := unitRange.comp g
  (injectSummand .unit).comp g'

theorem inject_apply_self (i : Comp3) (x : principal (compK i)) :
    injectSummand i x i = x := by
  rw [injectSummand, LinearMap.single_apply, Pi.single_eq_same]

theorem missing_probe (b : H) (hb : ∀ h : H, compK .full*h=0 → b*h=0) :
    (missingEnd b hb (injectSummand .full (rightGen (compK .full))) .unit : H) = b := by
  simp only [missingEnd, LinearMap.comp_apply, LinearMap.proj_apply,
    inject_apply_self]
  exact desc_generator (compK .full) b hb

def probe (f : C →ₗ[Hᵐᵒᵖ] C) : H :=
  f (injectSummand .full (rightGen (compK .full))) .unit

theorem prescribed_End_equality_fails : ¬ Function.Surjective comparison := by
  obtain ⟨b,hb,hn⟩ := polynomial_strict
  have hb' (h : H) : compK .full*h=0 → b*h=0 := k_full.symm ▸ hb h
  intro h
  obtain ⟨q,hq⟩ := h (missingEnd b hb')
  have he := congrArg probe hq
  have hw : (q .unit .full : H) = b :=
    (comparison_probe q).symm.trans (he.trans (missing_probe b hb'))
  obtain ⟨d,hd⟩ := (q .unit .full).property.2
  exact hn ⟨d,(congrArg (d*·) k_full).symm.trans (hd.trans hw)⟩

#print axioms compositions_exact
#print axioms k_full
#print axioms k_unit
#print axioms prescribed_product
#print axioms prescribed_End_equality_fails

end
end PolySkew
```

## TensorPolynomial.lean

```lean
import NativePresentation
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.TensorProduct.Maps

namespace PolySkew

open FiniteSkew
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 1500000

abbrev AP (U M : Type*) [Semiring U] := AddMonoidAlgebra U M

section TensorPoly
variable {U V' M N : Type*} [Ring U] [Ring V'] [Algebra ℚ U] [Algebra ℚ V']
    [AddMonoid M] [AddMonoid N]

def combine : (AP U M ⊗[ℚ] AP V' N) ≃ₗ[ℚ] AP (U ⊗[ℚ] V') (M × N) :=
  TensorProduct.congr (AddMonoidAlgebra.coeffLinearEquiv ℚ)
    (AddMonoidAlgebra.coeffLinearEquiv ℚ) ≪≫ₗ
    finsuppTensorFinsupp ℚ ℚ U V' M N ≪≫ₗ (AddMonoidAlgebra.coeffLinearEquiv ℚ).symm

omit [AddMonoid M] [AddMonoid N] in
@[simp] theorem combine_mono (m : M) (n : N) (u : U) (v : V') :
    combine (AddMonoidAlgebra.single m u ⊗ₜ[ℚ] AddMonoidAlgebra.single n v) =
      AddMonoidAlgebra.single (m,n) (u ⊗ₜ[ℚ] v) := by
  unfold combine
  simp [finsuppTensorFinsupp_single]

theorem combine_mul_pure (a c : AP U M) (b d : AP V' N) :
    combine ((a ⊗ₜ[ℚ] b) * (c ⊗ₜ[ℚ] d)) =
      combine (a ⊗ₜ[ℚ] b) * combine (c ⊗ₜ[ℚ] d) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul]
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a f ha hf =>
    simp only [add_mul, TensorProduct.add_tmul, map_add, ha, hf]
  | single m u =>
    induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add b f hb hf =>
      simp only [add_mul, TensorProduct.tmul_add, map_add, hb, hf]
    | single n v =>
      induction c using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add c f hc hf =>
        simp only [mul_add, TensorProduct.add_tmul, map_add, hc, hf]
      | single p w =>
        induction d using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add d f hd hf =>
          simp only [mul_add, TensorProduct.tmul_add, map_add, hd, hf]
        | single q x =>
          simp only [AddMonoidAlgebra.single_mul_single, combine_mono,
            Algebra.TensorProduct.tmul_mul_tmul]
          rfl

theorem combine_mul (a b : AP U M ⊗[ℚ] AP V' N) :
    combine (a*b) = combine a * combine b := by
  induction a using TensorProduct.inductionOn with
  | add a c ha hc => simp only [add_mul,map_add,ha,hc]
  | tmul a c =>
    induction b using TensorProduct.inductionOn with
    | add b d hb hd => simp only [mul_add,map_add,hb,hd]
    | tmul b d => exact combine_mul_pure a b c d

def combineAlg : (AP U M ⊗[ℚ] AP V' N) ≃ₐ[ℚ] AP (U ⊗[ℚ] V') (M × N) :=
  AlgEquiv.ofLinearEquiv combine
    (by simp only [Algebra.TensorProduct.one_def, AddMonoidAlgebra.one_def, combine_mono]; rfl)
    combine_mul

@[simp] theorem combineAlg_mono (m : M) (n : N) (u : U) (v : V') :
    combineAlg (AddMonoidAlgebra.single m u ⊗ₜ[ℚ] AddMonoidAlgebra.single n v) =
      AddMonoidAlgebra.single (m,n) (u ⊗ₜ[ℚ] v) := combine_mono m n u v

end TensorPoly

def expTriples : ((ℕ × ℕ) × ℕ) ≃+ Exp where
  toFun m := ![m.1.1,m.1.2,m.2]
  invFun m := ((m 0,m 1),m 2)
  left_inv _ := rfl
  right_inv m := by funext i; fin_cases i <;> rfl
  map_add' m n := by funext i; fin_cases i <;> rfl

abbrev BPoly := AP F ℕ
abbrev Pair := F ⊗[ℚ] F
abbrev PairP := AP Pair (ℕ × ℕ)
abbrev NativeCube := (BPoly ⊗[ℚ] BPoly) ⊗[ℚ] BPoly

def cubePoly : NativeCube ≃ₐ[ℚ] A :=
  (Algebra.TensorProduct.congr (combineAlg (U := F) (V' := F) (M := ℕ) (N := ℕ)) (AlgEquiv.refl : BPoly ≃ₐ[ℚ] BPoly)).trans <|
  combineAlg.trans <|
  (AddMonoidAlgebra.domCongr ℚ _ expTriples).trans <|
  AddMonoidAlgebra.mapAlgEquiv ℚ _ tensorAlgebraEquiv.symm

theorem cubePoly_mono (m : Exp) (u : T) :
    cubePoly ((AddMonoidAlgebra.single (m 0) (atom (u 0) : F) ⊗ₜ[ℚ]
      AddMonoidAlgebra.single (m 1) (atom (u 1) : F)) ⊗ₜ[ℚ]
      AddMonoidAlgebra.single (m 2) (atom (u 2) : F)) = mono m (atom u) := by
  have hm : expTriples ((m 0,m 1),m 2) = m := expTriples.apply_symm_apply m
  unfold cubePoly
  simp [hm, AddMonoidAlgebra.mapAlgEquiv, ← mono_apply]
  rw [← semantics_atom]
  exact congrArg (mono m) (tensorAlgebraEquiv.symm_apply_apply (atom u))

def polynomialEquiv (R : Type*) [Ring R] : AP R ℕ ≃+* Polynomial R where
  toFun p := ⟨p⟩
  invFun p := p.toFinsupp
  left_inv _ := rfl
  right_inv p := by cases p; rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem polynomialEquiv_mono (R : Type*) [Ring R] (n : ℕ) (r : R) :
    polynomialEquiv R (AddMonoidAlgebra.single n r) = Polynomial.monomial n r :=
  Polynomial.ofFinsupp_single n r

def polynomialCoordinateBasis : Module.Basis (ℕ × B) ℚ BPoly :=
  Finsupp.basisSingleOne.map
    ((Finsupp.curryLinearEquiv ℚ).trans (AddMonoidAlgebra.coeffLinearEquiv ℚ).symm)

#print axioms combineAlg
#print axioms cubePoly
#print axioms cubePoly_mono
#print axioms polynomialCoordinateBasis

end
end PolySkew
```

## Admissibility.lean

```lean
import TensorPolynomial
import Mathlib.Algebra.Polynomial.Monic

namespace PolySkew

open FiniteSkew
open scoped TensorProduct
noncomputable section
set_option synthInstance.maxSize 1024

def flipPair : Pair ≃ₐ[ℚ] Pair := Algebra.TensorProduct.comm ℚ F F

def aBasis : F := atom B.a
def bBasis : F := atom B.b

def alphaPair : Pair := 1 + (aBasis ⊗ₜ[ℚ] bBasis - bBasis ⊗ₜ[ℚ] aBasis)

private theorem a_sq : aBasis*aBasis=0 := by
  simp [aBasis, basis_mul,mulB,out]

private theorem b_sq : bBasis*bBasis=0 := by
  simp [bBasis,basis_mul,mulB,out]

private theorem ba_zero : bBasis*aBasis=0 := by
  simp [aBasis,bBasis,basis_mul,mulB,out]

theorem radical_pair_sq :
    (aBasis ⊗ₜ[ℚ] bBasis - bBasis ⊗ₜ[ℚ] aBasis) *
      (aBasis ⊗ₜ[ℚ] bBasis - bBasis ⊗ₜ[ℚ] aBasis) = 0 := by
  simp [mul_sub, sub_mul, Algebra.TensorProduct.tmul_mul_tmul, a_sq,b_sq,ba_zero]

theorem flip_alpha :
    flipPair alphaPair = 1 - (aBasis ⊗ₜ[ℚ] bBasis - bBasis ⊗ₜ[ℚ] aBasis) := by
  simp only [alphaPair, flipPair, map_add,map_one,map_sub,Algebra.TensorProduct.comm_tmul]
  abel

theorem alpha_inverse :
    alphaPair * flipPair alphaPair = 1 ∧ flipPair alphaPair * alphaPair = 1 := by
  rw [flip_alpha,alphaPair]
  generalize he : (aBasis ⊗ₜ[ℚ] bBasis - bBasis ⊗ₜ[ℚ] aBasis) = z
  have hz : z*z = 0 := he ▸ radical_pair_sq
  constructor
  · rw [add_mul, one_mul, mul_sub, mul_one, hz, sub_zero]
    abel
  · rw [mul_add, mul_one, sub_mul, one_mul, hz, sub_zero]
    abel

def pairPoly : (BPoly ⊗[ℚ] BPoly) ≃ₐ[ℚ] PairP := combineAlg

def pairConstant : Pair →+* PairP where
  toFun := AddMonoidAlgebra.single (0,0)
  map_zero' := AddMonoidAlgebra.single_zero _
  map_add' := AddMonoidAlgebra.single_add _
  map_one' := rfl
  map_mul' a b := by rw [AddMonoidAlgebra.single_mul_single]; rfl

def pairX : PairP := AddMonoidAlgebra.single (1,0) 1
def pairY : PairP := AddMonoidAlgebra.single (0,1) 1

def pairCurry : PairP ≃+* Polynomial (Polynomial Pair) :=
  (AddMonoidAlgebra.curryRingEquiv (R := Pair) (M := ℕ) (N := ℕ)).trans <|
  (polynomialEquiv (AP Pair ℕ)).trans <|
  Polynomial.mapEquiv (polynomialEquiv Pair)

local instance pairRing : Ring Pair := inferInstance
local instance pairPolynomialRing : Ring (Polynomial Pair) := Polynomial.ring
local instance nestedPairPolynomialRing : Ring (Polynomial (Polynomial Pair)) := Polynomial.ring

theorem pair_curry_diff :
    pairCurry (pairX-pairY) = (Polynomial.X : Polynomial (Polynomial Pair)) - Polynomial.C (Polynomial.X : Polynomial Pair) := by
  simp [pairCurry, pairX, pairY, polynomialEquiv_mono, Polynomial.X]

def BiRegular {R : Type*} [Mul R] [Zero R] (p : R) : Prop :=
  (∀ q, p*q=0 → q=0) ∧ (∀ q, q*p=0 → q=0)

theorem monic_regular {R : Type*} [Ring R] (p : Polynomial R) (hp : p.Monic) :
    BiRegular p := by
  constructor
  · intro q hz
    by_contra hq
    have he : p.leadingCoeff*q.leadingCoeff ≠ 0 := by
      rw [hp.leadingCoeff, one_mul]
      exact mt Polynomial.leadingCoeff_eq_zero.mp hq
    have hh := Polynomial.leadingCoeff_mul' he
    rw [hz, Polynomial.leadingCoeff_zero] at hh
    exact he hh.symm
  · intro q hz
    by_contra hq
    have he : q.leadingCoeff*p.leadingCoeff ≠ 0 := by
      rw [hp.leadingCoeff, mul_one]
      exact mt Polynomial.leadingCoeff_eq_zero.mp hq
    have hh := Polynomial.leadingCoeff_mul' he
    rw [hz, Polynomial.leadingCoeff_zero] at hh
    exact he hh.symm

theorem pair_diff_regular : BiRegular (pairX-pairY) := by
  obtain ⟨hl,hr⟩ := monic_regular _ (Polynomial.monic_X_sub_C (Polynomial.X : Polynomial Pair))
  constructor
  · intro q he
    apply pairCurry.injective
    rw [map_zero]
    apply hl
    rw [← pair_curry_diff, ← map_mul, he, map_zero]
  · intro q he
    apply pairCurry.injective
    rw [map_zero]
    apply hr
    rw [← pair_curry_diff, ← map_mul, he, map_zero]

def delta : Fin 2 → Fin 2 → Pair := fun _ _ => 0

def beta : PairP :=
  ∑ i : Fin 2, ∑ j : Fin 2, AddMonoidAlgebra.single (i.val,j.val) (delta i j)

def scalarR : Pair := 1
def scalarS : Pair := delta 1 0 - delta 0 1

@[simp] theorem beta_zero : beta = 0 := by simp [beta,delta]
@[simp] theorem scalarS_zero : scalarS = 0 := by simp [scalarS,delta]

def pairSwap : (ℕ × ℕ) ≃+ (ℕ × ℕ) where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def pairSigma : PairP ≃ₐ[ℚ] PairP :=
  (AddMonoidAlgebra.domCongr ℚ _ pairSwap).trans
    (AddMonoidAlgebra.mapAlgEquiv ℚ _ flipPair)

def rhoPair : PairP →ₗ[ℚ] PairP := 0

def deltaFirst : Pair →ₐ[ℚ] AbstractCube := Algebra.TensorProduct.includeLeft
def deltaSecond : Pair →ₐ[ℚ] AbstractCube :=
  (Algebra.TensorProduct.assoc ℚ ℚ ℚ F F F).symm.toAlgHom.comp
    Algebra.TensorProduct.includeRight

theorem c3 : BiRegular (pairConstant alphaPair*(pairX-pairY)+beta) := by
  rw [beta_zero,add_zero]
  have hL : pairConstant (flipPair alphaPair) * pairConstant alphaPair = 1 := by
    rw [← map_mul,alpha_inverse.2,map_one]
  have hR : pairConstant alphaPair * pairConstant (flipPair alphaPair) = 1 := by
    rw [← map_mul,alpha_inverse.1,map_one]
  constructor
  · intro q hz
    apply pair_diff_regular.1 q
    calc
      (pairX-pairY)*q = (pairConstant (flipPair alphaPair)*pairConstant alphaPair)*((pairX-pairY)*q) := by rw [hL,one_mul]
      _ = pairConstant (flipPair alphaPair) * ((pairConstant alphaPair * (pairX-pairY))*q) := by simp only [mul_assoc]
      _ = 0 := by rw [hz,mul_zero]
  · intro q hz
    have hq : q * pairConstant alphaPair = 0 := pair_diff_regular.2 _ (by simpa only [mul_assoc] using hz)
    rw [← mul_one q, ← hR, ← mul_assoc, hq, zero_mul]

def NativeAdmissible : Prop :=
  (∀ y : Pair, scalarR*y=y*scalarR) ∧ flipPair scalarR=scalarR ∧
  (∀ i j (a b : F), (a ⊗ₜ[ℚ] b) * delta i j = delta i j * (b ⊗ₜ[ℚ] a)) ∧
  (∀ i j, flipPair (delta i j)=delta i j) ∧
  deltaFirst (delta 0 0) * deltaSecond (delta 1 1) =
    deltaFirst (delta 0 1) * deltaSecond (delta 1 0) ∧
  pairSigma beta=beta ∧
  (∀ f : PairP, rhoPair f*(pairX-pairY)=beta*f-pairSigma f*beta) ∧
  alphaPair*(flipPair alphaPair+scalarS)=scalarR ∧
  BiRegular (pairConstant alphaPair*(pairX-pairY)+beta)

theorem native_admissible : NativeAdmissible := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,c3⟩
  · intro y; simp [scalarR]
  · simp [scalarR]
  · intro i j a b; simp [delta]
  · intro i j; simp [delta]
  · simp [delta]
  · simp
  · intro f; simp [rhoPair]
  · rw [scalarS_zero,add_zero,alpha_inverse.1]; rfl

theorem rho_unique (f q : PairP)
    (h : q*(pairX-pairY)=beta*f-pairSigma f*beta) : q = rhoPair f := by
  apply pair_diff_regular.2
  simpa [rhoPair] using h

theorem pair_sigma_mono (m n : ℕ) (a b : F) :
    pairSigma (pairPoly (AddMonoidAlgebra.single m a ⊗ₜ[ℚ] AddMonoidAlgebra.single n b)) =
      pairPoly (AddMonoidAlgebra.single n b ⊗ₜ[ℚ] AddMonoidAlgebra.single m a) := by
  simp [pairSigma, pairPoly, pairSwap, flipPair, AddMonoidAlgebra.mapAlgEquiv]

theorem joint_place_on_pure (g : P) (m : Exp) (u : T) :
    placePoly g (cubePoly ((AddMonoidAlgebra.single (m 0) (atom (u 0) : F) ⊗ₜ[ℚ]
      AddMonoidAlgebra.single (m 1) (atom (u 1) : F)) ⊗ₜ[ℚ]
      AddMonoidAlgebra.single (m 2) (atom (u 2) : F))) =
    cubePoly ((AddMonoidAlgebra.single ((move g m) 0) (atom ((place g u) 0) : F) ⊗ₜ[ℚ]
      AddMonoidAlgebra.single ((move g m) 1) (atom ((place g u) 1) : F)) ⊗ₜ[ℚ]
      AddMonoidAlgebra.single ((move g m) 2) (atom ((place g u) 2) : F)) := by
  simp only [cubePoly_mono, placePoly_mono, action_atom]

theorem variable_transport (g : P) (m : Exp) :
    sigmaUnit g * includeA (mono m 1) = includeA (mono (move g m) 1) * sigmaUnit g := by
  rw [wreath, placePoly_mono, action_unit]

theorem alpha_first_slots :
    tensorAlgebraEquiv (alpha 0 1) = deltaFirst alphaPair := by
  simp only [alpha,alphaPair,deltaFirst,map_add,map_sub,map_one,
    Algebra.TensorProduct.includeLeft_apply]
  have atom_eq (u : T) :
      tensorAlgebraEquiv (atom u) =
        ((atom (u 0) : F) ⊗ₜ[ℚ] atom (u 1)) ⊗ₜ[ℚ] atom (u 2) := semantics_atom u
  rw [atom_eq,atom_eq]
  have he : (atom B.one : F) = 1 := rfl
  simp [pairT,aBasis,bBasis,he,Algebra.TensorProduct.one_def]

#print axioms alpha_inverse
#print axioms native_admissible
#print axioms rho_unique
#print axioms pair_sigma_mono
#print axioms joint_place_on_pure
#print axioms variable_transport
#print axioms alpha_first_slots

end
end PolySkew
```

## SchurAlgebra.lean

```lean
import EndComparison

namespace PolySkew

open FiniteSkew
noncomputable section
set_option maxHeartbeats 1000000

def blockNumber (c : Comp3) (i : I) : ℕ :=
  ((c.parts.scanl (· + ·) 0).filter (· ≤ i.val)).length

theorem parabolic_exact (c : Comp3) :
    parabolic c = Finset.univ.filter
      (fun g : P => ∀ i : I, blockNumber c (g i) = blockNumber c i) := by
  cases c <;> decide

theorem orderedPairs_exact (c : Comp3) :
    orderedPairs c = lexPairs.filter
      (fun p => blockNumber c p.1 = blockNumber c p.2) := by
  cases c <;> decide

section Blocks
variable {R : Type*} [Ring R]

def blockZero (a b : R) : Block a b := ⟨0,⟨0,mul_zero _⟩,⟨0,zero_mul _⟩⟩

def blockAdd {a b : R} (x y : Block a b) : Block a b :=
  ⟨x.val+y.val, by
    obtain ⟨u,hu⟩ := x.property.1
    obtain ⟨v,hv⟩ := y.property.1
    exact ⟨u+v,by rw [mul_add,hu,hv]⟩, by
    obtain ⟨u,hu⟩ := x.property.2
    obtain ⟨v,hv⟩ := y.property.2
    exact ⟨u+v,by rw [add_mul,hu,hv]⟩⟩

def blockNeg {a b : R} (x : Block a b) : Block a b :=
  ⟨-x.val, by
    obtain ⟨u,hu⟩ := x.property.1
    exact ⟨-u,by rw [mul_neg,hu]⟩, by
    obtain ⟨u,hu⟩ := x.property.2
    exact ⟨-u,by rw [neg_mul,hu]⟩⟩

def blockDiag (a : R) : Block a a :=
  ⟨a,⟨1,mul_one a⟩,⟨1,one_mul a⟩⟩

theorem blockHom_eq {a b : R} (f g : principal b →ₗ[Rᵐᵒᵖ] principal a)
    (he : (f (rightGen b) : R) = (g (rightGen b) : R)) : f = g := by
  apply LinearMap.ext
  intro z
  obtain ⟨u,hu⟩ := principal_spec b z
  have hz : z = MulOpposite.op u • rightGen b := by
    apply Subtype.ext
    change (z:R) = (rightGen b : R)*u
    rw [rightGen_val,hu]
  rw [hz,map_smul,map_smul,Subtype.ext he]

theorem blockHom_zero (a b : R) : blockHom (blockZero a b) = 0 := by
  apply blockHom_eq
  rw [block_generator]
  rfl

theorem blockHom_add {a b : R} (x y : Block a b) :
    blockHom (blockAdd x y) = blockHom x + blockHom y := by
  apply blockHom_eq
  rw [block_generator, LinearMap.add_apply, Submodule.coe_add,block_generator,block_generator]
  rfl

theorem blockHom_neg {a b : R} (x : Block a b) :
    blockHom (blockNeg x) = -blockHom x := by
  apply blockHom_eq
  rw [block_generator, LinearMap.neg_apply, Submodule.coe_neg,block_generator]
  rfl

theorem blockHom_diag (a : R) : blockHom (blockDiag a) = LinearMap.id := by
  apply blockHom_eq
  rw [block_generator, LinearMap.id_apply, rightGen_val]
  rfl

theorem blockHom_comp {a b c : R} (x : Block a b) (y : Block b c) :
    blockHom (blockProduct x y) = (blockHom x).comp (blockHom y) := by
  apply blockHom_eq
  rw [block_generator,LinearMap.comp_apply]
  change (blockHom x ⟨y.val,y.property.1⟩ : R) =
    (blockHom x (blockHom y (rightGen c)) : R)
  congr 2
  apply Subtype.ext
  exact (block_generator y).symm

def blockSum {a b : R} {J : Type*} (s : Finset J) (q : J → Block a b) :
    Block a b :=
  ⟨∑ j ∈ s, (q j : R), by
    classical
    choose f hf using fun j => (q j).property.1
    exact ⟨∑ j ∈ s, f j, by rw [Finset.mul_sum]; simp only [hf]⟩, by
    classical
    choose f hf using fun j => (q j).property.2
    exact ⟨∑ j ∈ s, f j, by rw [Finset.sum_mul]; simp only [hf]⟩⟩

theorem blockHom_sum {a b : R} {J : Type*} (s : Finset J) (q : J → Block a b) :
    blockHom (blockSum s q) = ∑ j ∈ s, blockHom (q j) := by
  apply blockHom_eq
  rw [block_generator, LinearMap.sum_apply, Submodule.coe_sum]
  simp only [block_generator]
  rfl

end Blocks

def matrixZero : Intersection := fun i j => blockZero (compK i) (compK j)

def matrixOne : Intersection := fun i j =>
  if he : i = j then he ▸ blockDiag (compK i) else blockZero (compK i) (compK j)

def matrixAdd (p q : Intersection) : Intersection := fun i j => blockAdd (p i j) (q i j)

def matrixNeg (p : Intersection) : Intersection := fun i j => blockNeg (p i j)

def matrixMul (p q : Intersection) : Intersection :=
  fun i k => blockSum Finset.univ (fun j => blockProduct (p i j) (q j k))

theorem comparison_zero : comparison matrixZero = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  simp [comparison_apply,matrixZero,blockHom_zero]

theorem comparison_add (p q : Intersection) :
    comparison (matrixAdd p q) = comparison p + comparison q := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [LinearMap.add_apply, Pi.add_apply, comparison_apply,matrixAdd,
    blockHom_add,Finset.sum_add_distrib]

theorem comparison_neg (p : Intersection) :
    comparison (matrixNeg p) = -comparison p := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [LinearMap.neg_apply, Pi.neg_apply, comparison_apply,matrixNeg,
    blockHom_neg,Finset.sum_neg_distrib]

theorem comparison_one : comparison matrixOne = 1 := by
  apply LinearMap.ext
  intro x
  funext i
  rw [comparison_apply, Finset.sum_eq_single i]
  · simp [matrixOne,blockHom_diag]
  · intro j _ hj
    simp [matrixOne,Ne.symm hj,blockHom_zero]
  · simp

theorem comparison_mul (p q : Intersection) :
    comparison (matrixMul p q) = comparison p * comparison q := by
  apply LinearMap.ext
  intro x
  funext i
  change comparison (matrixMul p q) x i = comparison p (comparison q x) i
  simp only [comparison_apply,matrixMul,blockHom_sum,LinearMap.sum_apply,
    blockHom_comp,LinearMap.comp_apply,map_sum]
  exact Finset.sum_comm

theorem comparison_entry (q : Intersection) (i j : Comp3) :
    (comparison q (injectSummand j (rightGen (compK j))) i : H) = (q i j : H) := by
  rw [comparison_apply,Finset.sum_eq_single j]
  · rw [inject_apply_self,block_generator]
  · intro k _ hk
    simp [injectSummand,hk]
  · simp

theorem comparison_injective : Function.Injective comparison := by
  intro p q h
  funext i j
  apply Subtype.ext
  have he := congrArg (fun f : C →ₗ[Hᵐᵒᵖ] C =>
    (f (injectSummand j (rightGen (compK j))) i : H)) h
  rwa [comparison_entry,comparison_entry] at he

abbrev EndH := Module.End Hᵐᵒᵖ C

def statedIntersection : Subring EndH where
  carrier := Set.range comparison
  zero_mem' := ⟨matrixZero,comparison_zero⟩
  one_mem' := ⟨matrixOne,comparison_one⟩
  add_mem' := by
    rintro _ _ ⟨p,rfl⟩ ⟨q,rfl⟩
    exact ⟨matrixAdd p q,comparison_add p q⟩
  neg_mem' := by
    rintro _ ⟨p,rfl⟩
    exact ⟨matrixNeg p,comparison_neg p⟩
  mul_mem' := by
    rintro _ _ ⟨p,rfl⟩ ⟨q,rfl⟩
    exact ⟨matrixMul p q,comparison_mul p q⟩

def intersectionIdentification : Intersection ≃ statedIntersection :=
  Equiv.ofInjective comparison comparison_injective

theorem stated_intersection_ne_End : statedIntersection ≠ ⊤ := by
  intro h
  apply prescribed_End_equality_fails
  intro f
  change f ∈ statedIntersection
  rw [h]
  exact Subring.mem_top f

def rightAction (h : H) : AddMonoid.End C where
  toFun x := MulOpposite.op h • x
  map_zero' := smul_zero _
  map_add' _ _ := smul_add _ _ _

def intersectionCentralizer : Set (AddMonoid.End C) :=
  {f | ∀ q : Intersection, f.comp (comparison q).toAddMonoidHom =
    (comparison q).toAddMonoidHom.comp f}

def NativeDoubleCentralizer : Prop :=
  intersectionCentralizer = Set.range rightAction ∧ statedIntersection = ⊤

theorem native_double_centralizer_fails : ¬ NativeDoubleCentralizer :=
  fun h => stated_intersection_ne_End h.2

#print axioms parabolic_exact
#print axioms orderedPairs_exact
#print axioms comparison_mul
#print axioms intersectionIdentification
#print axioms stated_intersection_ne_End
#print axioms native_double_centralizer_fails

end
end PolySkew
```

## SkewOperators.lean

```lean
import Admissibility
import Mathlib.Algebra.MonoidAlgebra.Support

namespace PolySkew
open FiniteSkew
noncomputable section

def coeffOp : A →+* Module.End ℚ A where
  toFun a :=
    { toFun := (a * ·)
      map_add' := mul_add a
      map_smul' := fun r b => Algebra.mul_smul_comm r a b }
  map_zero' := by apply LinearMap.ext; intro b; exact zero_mul b
  map_one' := by apply LinearMap.ext; intro b; exact one_mul b
  map_add' a b := by apply LinearMap.ext; intro x; exact add_mul a b x
  map_mul' a b := by apply LinearMap.ext; intro x; exact mul_assoc a b x

def permOp : P →* Module.End ℚ A where
  toFun := placePoly
  map_one' := LinearMap.ext placePoly_one
  map_mul' g h := LinearMap.ext (placePoly_comp g h)

theorem operator_cross (g : P) (a : A) :
    permOp g * coeffOp a = coeffOp (placePoly g a) * permOp g :=
  LinearMap.ext (placePoly_mul g a)

def skewOp : H →+* Module.End ℚ A := lift coeffOp permOp operator_cross

theorem skewOp_apply (x : H) (a : A) :
    skewOp x a = ∑ g : P, leftCoeff g x * placePoly g a := by
  change liftAdd coeffOp permOp x a = _
  rw [liftAdd_apply,LinearMap.sum_apply]
  rfl

def spacing (N : ℕ) : Exp := fun i => i.val*N

theorem spacing_separates (N : ℕ) (u v : Exp) (g h : P)
    (hu : ∀ i, u i < N) (hv : ∀ i, v i < N)
    (he : u + move g (spacing N) = v + move h (spacing N)) : g = h := by
  have idx (a b : ℕ) (i j : I) (ha : a < N) (hb : b < N)
      (heq : a + spacing N i = b + spacing N j) : i = j := by
    fin_cases i <;> fin_cases j <;> simp [spacing] at heq ⊢ <;> omega
  have invEq : g⁻¹ = h⁻¹ := by
    apply Equiv.ext
    intro i
    exact idx (u i) (v i) (g⁻¹ i) (h⁻¹ i) (hu i) (hv i) (congrFun he i)
  exact inv_injective invEq

def bound (x : H) : ℕ :=
  (Finset.univ : Finset P).sup
    (fun g => (leftCoeff g x).coeff.support.sup (fun e => ∑ i : I, e i)) + 1

theorem exponent_lt_bound (x : H) (g : P) (e : Exp)
    (he : e ∈ (leftCoeff g x).coeff.support) (i : I) :
    e i < bound x := by
  have h1 : e i ≤ ∑ i : I, e i :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
  have h2 : (∑ i : I, e i) ≤
      (leftCoeff g x).coeff.support.sup (fun e => ∑ i : I, e i) :=
    Finset.le_sup (f := fun e : Exp => ∑ i : I, e i) he
  have h3 : (leftCoeff g x).coeff.support.sup (fun e => ∑ i : I, e i) ≤
      (Finset.univ : Finset P).sup
        (fun g => (leftCoeff g x).coeff.support.sup (fun e => ∑ i : I, e i)) :=
    Finset.le_sup (f := fun k : P => (leftCoeff k x).coeff.support.sup (fun e => ∑ i : I, e i))
      (Finset.mem_univ g)
  exact Nat.lt_succ_of_le (h1.trans (h2.trans h3))

theorem skewOp_mono (x : H) (m : Exp) :
    skewOp x (mono m 1) = ∑ g : P, leftCoeff g x * mono (move g m) 1 := by
  simp only [skewOp_apply,placePoly_mono,action_unit]

theorem skewOp_detect (x : H) (g : P) (e : Exp)
    (he : e ∈ (leftCoeff g x).coeff.support) :
    (skewOp x (mono (spacing (bound x)) 1)).coeff
      (e + move g (spacing (bound x))) = (leftCoeff g x).coeff e := by
  classical
  let m := spacing (bound x)
  let n := e + move g m
  change (skewOp x (mono m 1)).coeff n = _
  rw [skewOp_mono]
  simp only [AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single g]
  · change ((leftCoeff g x) * AddMonoidAlgebra.single (move g m) 1).coeff _ = _
    rw [AddMonoidAlgebra.coeff_mul_single_add,mul_one]
  · intro h _ hh
    apply Finsupp.notMem_support_iff.mp
    intro hn
    have hin := AddMonoidAlgebra.support_coeff_mul_single_subset (leftCoeff h x) (1 : Tensor) (move h m) hn
    obtain ⟨f,hf,hn'⟩ := Finset.mem_image.mp hin
    exact hh (spacing_separates _ f e h g
      (exponent_lt_bound x h f hf) (exponent_lt_bound x g e he) hn')
  · simp

theorem skewOp_faithful : Function.Injective skewOp := by
  apply (injective_iff_map_eq_zero skewOp).mpr
  intro x hx
  have hc (g : P) : leftCoeff g x = 0 := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro e
    by_contra! he
    have hs : e ∈ (leftCoeff g x).coeff.support := Finsupp.mem_support_iff.mpr (by simpa using he)
    have h := skewOp_detect x g e hs
    rw [hx] at h
    exact he (by simpa using h.symm)
  rw [left_normal x]
  simp [hc]

#print axioms skewOp_apply
#print axioms skewOp_faithful

end
end PolySkew
```

## FixedPair.lean

```lean
import SchurAlgebra
import SkewOperators

namespace PolySkew

open FiniteSkew
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 1500000

def iotaAlg : D →ₐ[ℚ] H where
  __ := iota
  commutes' q := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change rightTerm 0 (q • 1) = q • 1
    rw [map_smul]
    exact congrArg (q • ·) iota.map_one

def augmentAlg : H →ₐ[ℚ] D where
  __ := augment
  commutes' q := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change rightCoeff (q • 1) 0 = q • 1
    rw [rightCoeff_smul]
    exact congrArg (q • ·) augment.map_one

theorem alg_retraction : augmentAlg.comp iotaAlg = AlgHom.id ℚ D := by
  apply AlgHom.ext
  exact augment_iota

theorem iota_injective : Function.Injective iotaAlg := by
  intro d e he
  exact (augment_iota d).symm.trans ((congrArg augment he).trans (augment_iota e))

theorem variable_adjoint (g : P) (m : Exp) :
    (sigmaUnit g * includeA (mono m 1)) * sigmaUnit g⁻¹ =
      includeA (mono (move g m) 1) := by
  rw [variable_transport,mul_assoc,← sigmaUnit.map_mul,mul_inv_cancel,sigmaUnit.map_one,mul_one]

def nativeTensorInclude : NativeCube →+* H := includeA.comp cubePoly.toRingHom

def nativePlace (g : P) : NativeCube ≃+* NativeCube :=
  cubePoly.toRingEquiv.trans ((placePolyAut g).trans cubePoly.symm.toRingEquiv)

theorem nativePlace_binding (g : P) (a : NativeCube) :
    cubePoly (nativePlace g a) = placePoly g (cubePoly a) :=
  cubePoly.apply_symm_apply _

theorem native_tensor_wreath (g : P) (a : NativeCube) :
    sigmaUnit g * nativeTensorInclude a = nativeTensorInclude (nativePlace g a) * sigmaUnit g := by
  change sigmaUnit g * includeA (cubePoly a) = includeA (cubePoly (nativePlace g a)) * sigmaUnit g
  rw [nativePlace_binding]
  exact wreath g _

theorem native_tensor_presentation {R : Type*} [Ring R]
    (c : NativeCube →+* R) (u v : R)
    (usq : u*u=1) (vsq : v*v=1) (br : u*v*u=v*u*v)
    (cs : ∀ a, u*c a = c (nativePlace s a)*u)
    (ct : ∀ a, v*c a = c (nativePlace t a)*v) :
    ∃! f : H →+* R, (∀ a, f (nativeTensorInclude a) = c a) ∧
      f (sigmaUnit s) = u ∧ f (sigmaUnit t) = v := by
  let c' : A →+* R := c.comp cubePoly.symm.toRingHom
  have cv (g : P) (a : A) : nativePlace g (cubePoly.symm a) = cubePoly.symm (placePoly g a) := by
    apply cubePoly.injective
    rw [nativePlace_binding, cubePoly.apply_symm_apply, cubePoly.apply_symm_apply]
  have hs (a : A) : u*c' a = c' (placePoly s a)*u := by
    change u*c (cubePoly.symm a) = c (cubePoly.symm (placePoly s a))*u
    rw [cs,cv]
  have ht (a : A) : v*c' a = c' (placePoly t a)*v := by
    change v*c (cubePoly.symm a) = c (cubePoly.symm (placePoly t a))*v
    rw [ct,cv]
  obtain ⟨f,hf,unique⟩ := nativePresentation c' u v usq vsq br hs ht
  refine ⟨f,⟨?_,hf.2⟩,?_⟩
  · intro a
    change f (includeA (cubePoly a)) = c a
    rw [hf.1]
    change c (cubePoly.symm (cubePoly a)) = c a
    rw [cubePoly.symm_apply_apply]
  · intro k hk
    apply unique
    refine ⟨?_, hk.2⟩
    intro a
    have he := hk.1 (cubePoly.symm a)
    change k (includeA (cubePoly (cubePoly.symm a))) = c' a at he
    rwa [cubePoly.apply_symm_apply] at he

theorem action_alpha (g : P) (i k : I) : action g (alpha i k) = alpha (g i) (g k) := by
  have he : reindex (place g) (1:Tensor) = 1 := action_unit g
  simp only [alpha, action, map_add, map_sub, reindex_atom, action_pair, he]

def cubeAlpha (i k : I) : NativeCube := cubePoly.symm (mono 0 (alpha i k))

theorem cubeAlpha_transport (g : P) (i k : I) :
    nativePlace g (cubeAlpha i k) = cubeAlpha (g i) (g k) := by
  apply cubePoly.injective
  rw [nativePlace_binding]
  simp only [cubeAlpha, cubePoly.apply_symm_apply, placePoly_mono, move_zero,action_alpha]

def monoZero : Tensor →+* A where
  toFun := mono 0
  map_zero' := map_zero _
  map_one' := rfl
  map_add' := map_add _
  map_mul' a b := by
    change mono 0 (a*b) = mono 0 a * mono 0 b
    rw [mono_mul, zero_add]

theorem ordered_product_native (xs : List (I × I)) :
    cubePoly ((xs.map fun p => cubeAlpha p.1 p.2).prod) =
      mono 0 ((xs.map fun p => alpha p.1 p.2).prod) := by
  induction xs with
  | nil => simp only [List.map_nil,List.prod_nil,map_one,poly_one]
  | cons p xs ih =>
    simp only [List.map_cons,List.prod_cons,map_mul,ih]
    rw [cubeAlpha,cubePoly.apply_symm_apply,mono_mul,zero_add]

theorem native_tensor_K (c : Comp3) :
    compK c = ∑ g ∈ parabolic c, nativeTensorInclude
      (((orderedPairs c).filter (fun p => g p.1 < g p.2)).map
        (fun p => cubeAlpha p.1 p.2)).prod * sigmaUnit g := by
  unfold compK
  refine Finset.sum_congr rfl fun g _ => ?_
  change _ = includeA (cubePoly _) * sigmaUnit g
  rw [ordered_product_native]

private theorem noncentral_tensor :
    alpha 0 1 * (atom ![B.a,B.one,B.one] : Tensor) -
      atom ![B.a,B.one,B.one] * alpha 0 1 = atom ![B.c,B.a,B.one] := by
  have e1 : mulT (pairT 0 1 B.a B.b) ![B.a,B.one,B.one] = none := by decide
  have e2 : mulT (pairT 0 1 B.b B.a) ![B.a,B.one,B.one] = none := by decide
  have e3 : mulT (![B.a,B.one,B.one]) (pairT 0 1 B.a B.b) = none := by decide
  have e4 : mulT (![B.a,B.one,B.one]) (pairT 0 1 B.b B.a) =
      some ![B.c,B.a,B.one] := by decide
  rw [alpha,add_mul,sub_mul,mul_add,mul_sub,one_mul,mul_one,
    tensor_mul,tensor_mul,tensor_mul,tensor_mul,e1,e2,e3,e4]
  simp [out]

theorem alpha_not_central : ¬ ∀ y : Pair, alphaPair*y=y*alphaPair := by
  intro h
  have ha : tensorAlgebraEquiv (atom ![B.a,B.one,B.one]) =
      deltaFirst (aBasis ⊗ₜ[ℚ] (1:F)) := by
    change tensorSemantics (atom ![B.a,B.one,B.one]) = _
    rw [semantics_atom,deltaFirst,Algebra.TensorProduct.includeLeft_apply]
    rfl
  have hc : alpha 0 1 * (atom ![B.a,B.one,B.one] : Tensor) -
      atom ![B.a,B.one,B.one] * alpha 0 1 = 0 := by
    apply tensorAlgebraEquiv.injective
    rw [map_zero,map_sub,map_mul,map_mul,alpha_first_slots,ha,
      ← map_mul,← map_mul,h,sub_self]
  rw [noncentral_tensor] at hc
  have he := congrArg (fun (x : Tensor) => x ![B.c,B.a,B.one]) hc
  change (Finsupp.single (![B.c,B.a,B.one] : T) (1 : ℚ)) _ = 0 at he
  rw [Finsupp.single_eq_same] at he
  exact one_ne_zero he

theorem fixed_pair_native_refutation :
    NativeAdmissible ∧ ¬ NativeDoubleCentralizer :=
  ⟨native_admissible,native_double_centralizer_fails⟩

theorem fixed_pair_prescribed_End_inequality :
    NativeAdmissible ∧ statedIntersection ≠ (⊤ : Subring EndH) :=
  ⟨native_admissible,stated_intersection_ne_End⟩

#print axioms alg_retraction
#print axioms iota_injective
#print axioms variable_adjoint
#print axioms native_tensor_presentation
#print axioms native_tensor_K
#print axioms alpha_not_central
#print axioms fixed_pair_native_refutation
#print axioms fixed_pair_prescribed_End_inequality

#eval Lean.versionString

end
end PolySkew
```

## Endpoint.lean

```lean
import FixedPair
import Mathlib.Algebra.DirectSum.Module

namespace PolySkew
open FiniteSkew
open scoped TensorProduct DirectSum
noncomputable section
set_option maxHeartbeats 1500000

instance : Fintype B where
  elems := {.one,.a,.b,.c,.z}
  complete i := by cases i <;> simp

theorem ordinary_rank_five : Fintype.card B = 5 := by decide

def nativeTensorIncludeAlg : NativeCube →ₐ[ℚ] H where
  __ := nativeTensorInclude
  commutes' q := by
    rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one]
    change leftTerm 1 (cubePoly (q • 1)) = q • 1
    rw [map_smul,map_smul]
    exact congrArg (q • ·) nativeTensorInclude.map_one

theorem nativeTensorInclude_injective : Function.Injective nativeTensorIncludeAlg := by
  intro x y h
  apply cubePoly.injective
  exact leftTerm_injective 1 h

theorem native_algebra_presentation {R : Type*} [Ring R] [Algebra ℚ R]
    (c : NativeCube →ₐ[ℚ] R) (u v : R)
    (usq : u*u=1) (vsq : v*v=1) (br : u*v*u=v*u*v)
    (cs : ∀ a, u*c a = c (nativePlace s a)*u)
    (ct : ∀ a, v*c a = c (nativePlace t a)*v) :
    ∃! f : H →ₐ[ℚ] R, (∀ a, f (nativeTensorIncludeAlg a) = c a) ∧
      f (sigmaUnit s) = u ∧ f (sigmaUnit t) = v := by
  obtain ⟨f,hf,unique⟩ := native_tensor_presentation c.toRingHom u v usq vsq br cs ct
  let f' : H →ₐ[ℚ] R := {
    __ := f
    commutes' := fun q => by
      rw [← nativeTensorIncludeAlg.commutes q]
      exact (hf.1 _).trans (c.commutes q) }
  refine ⟨f',hf,?_⟩
  intro k hk
  have he : k.toRingHom = f := unique k.toRingHom hk
  apply AlgHom.ext
  intro x
  exact DFunLike.congr_fun he x

theorem tensor_pair_variables :
    pairPoly ((AddMonoidAlgebra.single 1 (1:F)) ⊗ₜ[ℚ] (1:BPoly)) = pairX ∧
    pairPoly ((1:BPoly) ⊗ₜ[ℚ] (AddMonoidAlgebra.single 1 (1:F))) = pairY := by
  simp [pairPoly,pairX,pairY,AddMonoidAlgebra.one_def,Algebra.TensorProduct.one_def]

abbrev CDirect := ⨁ i : Comp3, ↥(principal (compK i))

def directSumModel : CDirect ≃ₗ[Hᵐᵒᵖ] C :=
  DirectSum.linearEquivFunOnFintype Hᵐᵒᵖ Comp3 (fun i => ↥(principal (compK i)))

theorem direct_sum_injection (i : Comp3) (x : principal (compK i)) :
    directSumModel (DirectSum.lof Hᵐᵒᵖ Comp3 (fun i => ↥(principal (compK i))) i x) =
      injectSummand i x := by
  rw [directSumModel,DirectSum.linearEquivFunOnFintype_lof]
  rfl

def directComparison (q : Intersection) : CDirect →ₗ[Hᵐᵒᵖ] CDirect :=
  directSumModel.symm.toLinearMap.comp ((comparison q).comp directSumModel.toLinearMap)

theorem native_direct_sum_End_equality_fails : ¬ Function.Surjective directComparison := by
  intro hs
  apply prescribed_End_equality_fails
  intro f
  let f' : CDirect →ₗ[Hᵐᵒᵖ] CDirect :=
    directSumModel.symm.toLinearMap.comp (f.comp directSumModel.toLinearMap)
  obtain ⟨q,hq⟩ := hs f'
  refine ⟨q,?_⟩
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun hq (directSumModel.symm x)
  apply directSumModel.symm.injective
  simpa only [directComparison,f',LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using h

theorem MathDB366949_counterexample :
    NativeAdmissible ∧ ¬ NativeDoubleCentralizer ∧ ¬ Function.Surjective directComparison :=
  ⟨native_admissible, native_double_centralizer_fails, native_direct_sum_End_equality_fails⟩

#print axioms native_algebra_presentation
#print axioms tensor_pair_variables
#print axioms direct_sum_injection
#print axioms native_direct_sum_End_equality_fails
#print axioms MathDB366949_counterexample

end
end PolySkew
```

