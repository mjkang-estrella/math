import Research.Problem

/-! A completely finite short-Weierstrass example over F₅.

The curve y² = x³ + 2x + 1 has six affine points and infinity. Addition
computes slopes from coordinates; no scalar-to-point or inverse-log table is
used by the executable operations or public encoding. `enumerate` is a finite
proof device listing ordinary coordinates, not an implementation of addition.
The claims here concern this seven-point example only, not secp256k1, a
growing family, an ECDLP solver, or any cost bound.
-/
namespace Research.SmallCurve

abbrev F := Fin 5
abbrev RawPoint := Option (F × F)

def fadd (a b : F) : F := ⟨(a.val + b.val) % 5, Nat.mod_lt _ (by decide)⟩
def fsub (a b : F) : F := ⟨(a.val + 5 - b.val) % 5, Nat.mod_lt _ (by decide)⟩
def fmul (a b : F) : F := ⟨(a.val * b.val) % 5, Nat.mod_lt _ (by decide)⟩
def finv (a : F) : F := ⟨a.val ^ 3 % 5, Nat.mod_lt _ (by decide)⟩

def OnCurve : RawPoint → Prop
  | none => True
  | some (x, y) => (y.val * y.val) % 5 = (x.val ^ 3 + 2 * x.val + 1) % 5

instance (p : RawPoint) : Decidable (OnCurve p) := by
  cases p with
  | none => exact inferInstanceAs (Decidable True)
  | some p => exact inferInstanceAs (Decidable (_ = _))

/-- The short-Weierstrass discriminant factor 4a³+27b² is nonzero in F₅.
Since 5 is neither 2 nor 3, this is the conventional nonsingularity test. -/
theorem discriminant_nonzero : (4 * 2 ^ 3 + 27 * 1 ^ 2) % 5 ≠ 0 := by
  decide +kernel

/-- Rational-point derivative check for the homogeneous equation
Y²Z = X³ + 2XZ² + Z³: at every nonzero F₅ coordinate triple satisfying the
equation, at least one of its three formal partial derivatives is nonzero.
The final disjunct writes ∂/∂Z = Y² - 4XZ - 3Z² without Nat subtraction.
This includes infinity but quantifies only over F₅, not extension fields.
Geometric smoothness follows from `discriminant_nonzero` by the standard
criterion, which is not formalized here. No projective quotient is constructed. -/
theorem homogeneous_nonsingular : ∀ x y z : F,
    (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) →
    (y.val ^ 2 * z.val) % 5 =
      (x.val ^ 3 + 2 * x.val * z.val ^ 2 + z.val ^ 3) % 5 →
    (3 * x.val ^ 2 + 2 * z.val ^ 2) % 5 ≠ 0 ∨
      (2 * y.val * z.val) % 5 ≠ 0 ∨
      y.val ^ 2 % 5 ≠ (4 * x.val * z.val + 3 * z.val ^ 2) % 5 := by
  decide +kernel

theorem nonzero_inverse : ∀ a : F, a ≠ 0 → fmul a (finv a) = 1 := by
  decide +kernel

/-- Coordinate slope formula for a finite output. -/
def slopePoint (x y u : F) (s : F) : RawPoint :=
  let v := fsub (fsub (fmul s s) x) u
  some (v, fsub (fmul s (fsub x v)) y)

/-- Affine addition, including infinity, vertical lines, and tangency.
The inverse is computed as t³ in F₅, justified by `nonzero_inverse`. -/
def rawAdd : RawPoint → RawPoint → RawPoint
  | none, q => q
  | p, none => p
  | some (x, y), some (u, v) =>
      if x = u then
        if fadd y v = 0 then none
        else slopePoint x y u
          (fmul (fadd (fmul 3 (fmul x x)) 2) (finv (fmul 2 y)))
      else slopePoint x y u (fmul (fsub v y) (finv (fsub u x)))

def rawNeg : RawPoint → RawPoint
  | none => none
  | some (x, y) => some (x, fsub 0 y)

theorem secant_formula (x y u v : F) (h : x ≠ u) :
    rawAdd (some (x, y)) (some (u, v)) =
      slopePoint x y u (fmul (fsub v y) (finv (fsub u x))) := by
  simp [rawAdd, h]

theorem tangent_formula (x y : F) (h : fadd y y ≠ 0) :
    rawAdd (some (x, y)) (some (x, y)) =
      slopePoint x y x
        (fmul (fadd (fmul 3 (fmul x x)) 2) (finv (fmul 2 y))) := by
  simp [rawAdd, h]

theorem vertical_formula (x y v : F) (h : fadd y v = 0) :
    rawAdd (some (x, y)) (some (x, v)) = none := by
  simp [rawAdd, h]

/-- Exhaustive list of curve points, solely for finite kernel proofs. -/
def enumerate (i : Fin 7) : RawPoint :=
  match i.val with
  | 0 => none
  | 1 => some (0, 1)
  | 2 => some (0, 4)
  | 3 => some (1, 2)
  | 4 => some (1, 3)
  | 5 => some (3, 2)
  | _ => some (3, 3)

theorem enumerate_onCurve : ∀ i : Fin 7, OnCurve (enumerate i) := by
  decide +kernel

private theorem affine_complete : ∀ x y : F,
    OnCurve (some (x, y)) → ∃ i : Fin 7, enumerate i = some (x, y) := by
  decide +kernel

theorem enumerate_complete (p : RawPoint) (h : OnCurve p) :
    ∃ i : Fin 7, enumerate i = p := by
  cases p with
  | none => exact ⟨0, rfl⟩
  | some p => exact affine_complete p.1 p.2 h

private theorem finite_closed : ∀ i j : Fin 7,
    OnCurve (rawAdd (enumerate i) (enumerate j)) := by
  decide +kernel

theorem rawAdd_closed (p q : RawPoint) (hp : OnCurve p) (hq : OnCurve q) :
    OnCurve (rawAdd p q) := by
  obtain ⟨i, rfl⟩ := enumerate_complete p hp
  obtain ⟨j, rfl⟩ := enumerate_complete q hq
  exact finite_closed i j

private theorem finite_neg_closed : ∀ i : Fin 7,
    OnCurve (rawNeg (enumerate i)) := by
  decide +kernel

theorem rawNeg_closed (p : RawPoint) (hp : OnCurve p) : OnCurve (rawNeg p) := by
  obtain ⟨i, rfl⟩ := enumerate_complete p hp
  exact finite_neg_closed i

abbrev Point := {p : RawPoint // OnCurve p}

def infinity : Point := ⟨none, trivial⟩
def add (p q : Point) : Point := ⟨rawAdd p.val q.val, rawAdd_closed _ _ p.property q.property⟩
def neg (p : Point) : Point := ⟨rawNeg p.val, rawNeg_closed _ p.property⟩
def generator : Point := ⟨some (0, 1), by decide⟩

theorem add_coordinates (p q : Point) : (add p q).val = rawAdd p.val q.val := rfl

private theorem finite_assoc : ∀ i j k : Fin 7,
    rawAdd (rawAdd (enumerate i) (enumerate j)) (enumerate k) =
      rawAdd (enumerate i) (rawAdd (enumerate j) (enumerate k)) := by
  decide +kernel

theorem add_assoc (p q r : Point) : add (add p q) r = add p (add q r) := by
  apply Subtype.ext
  obtain ⟨i, hi⟩ := enumerate_complete p.val p.property
  obtain ⟨j, hj⟩ := enumerate_complete q.val q.property
  obtain ⟨k, hk⟩ := enumerate_complete r.val r.property
  change rawAdd (rawAdd p.val q.val) r.val = rawAdd p.val (rawAdd q.val r.val)
  rw [← hi, ← hj, ← hk]
  exact finite_assoc i j k

private theorem finite_comm : ∀ i j : Fin 7,
    rawAdd (enumerate i) (enumerate j) = rawAdd (enumerate j) (enumerate i) := by
  decide +kernel

theorem add_comm (p q : Point) : add p q = add q p := by
  apply Subtype.ext
  obtain ⟨i, hi⟩ := enumerate_complete p.val p.property
  obtain ⟨j, hj⟩ := enumerate_complete q.val q.property
  change rawAdd p.val q.val = rawAdd q.val p.val
  rw [← hi, ← hj]
  exact finite_comm i j

theorem infinity_add (p : Point) : add infinity p = p := by
  apply Subtype.ext
  rfl

theorem add_infinity (p : Point) : add p infinity = p := by
  rw [add_comm, infinity_add]

private theorem finite_inverse : ∀ i : Fin 7,
    rawAdd (enumerate i) (rawNeg (enumerate i)) = none := by
  decide +kernel

theorem add_neg (p : Point) : add p (neg p) = infinity := by
  apply Subtype.ext
  obtain ⟨i, hi⟩ := enumerate_complete p.val p.property
  change rawAdd p.val (rawNeg p.val) = none
  rw [← hi]
  exact finite_inverse i

def next (p : Point) : Point := add p generator
def multiple (n : Nat) : Point := iteratePoint next infinity n

theorem order_wraps : multiple 7 = infinity := by
  decide +kernel

theorem orbit_distinct : ∀ i j : Fin 7, multiple i.val = multiple j.val → i = j := by
  decide +kernel

/-- No positive scalar below seven sends the generator orbit to infinity. -/
theorem exact_order : ∀ n : Fin 7, 0 < n.val → multiple n.val ≠ infinity := by
  decide +kernel

private theorem finite_orbit_complete : ∀ i : Fin 7,
    ∃ n : Fin 7, (multiple n.val).val = enumerate i := by
  decide +kernel

/-- The generator orbit exhausts the entire curve, not just a subgroup. -/
theorem orbit_complete (p : Point) : ∃ n : Fin 7, multiple n.val = p := by
  obtain ⟨i, hi⟩ := enumerate_complete p.val p.property
  obtain ⟨n, hn⟩ := finite_orbit_complete i
  refine ⟨n, Subtype.ext ?_⟩
  exact hn.trans hi

/-- A fixed seven-bit encoding: infinity/affine tag, then two three-bit
little-endian coordinate residues. Infinity uses zero coordinate padding. -/
def encodeRaw : RawPoint → List Bool
  | none => false :: (bits 3 0 ++ bits 3 0)
  | some (x, y) => true :: (bits 3 x.val ++ bits 3 y.val)

def encode (p : Point) : List Bool := encodeRaw p.val

private theorem finite_encoding_injective : ∀ i j : Fin 7,
    encodeRaw (enumerate i) = encodeRaw (enumerate j) → enumerate i = enumerate j := by
  decide +kernel

theorem encode_injective (p q : Point) (h : encode p = encode q) : p = q := by
  apply Subtype.ext
  obtain ⟨i, hi⟩ := enumerate_complete p.val p.property
  obtain ⟨j, hj⟩ := enumerate_complete q.val q.property
  change encodeRaw p.val = encodeRaw q.val at h
  rw [← hi, ← hj] at h ⊢
  exact finite_encoding_injective i j h

private theorem finite_encoding_width : ∀ i : Fin 7,
    (encodeRaw (enumerate i)).length = 7 := by
  decide +kernel

theorem encode_width (p : Point) : (encode p).length = 7 := by
  obtain ⟨i, hi⟩ := enumerate_complete p.val p.property
  change (encodeRaw p.val).length = 7
  rw [← hi]
  exact finite_encoding_width i

/-- Fixed public header: three-bit little-endian p, a, b, Gx, Gy, q.
The schema and field widths are fixed in this module. -/
def parameters : List Bool :=
  bits 3 5 ++ bits 3 2 ++ bits 3 1 ++ bits 3 0 ++ bits 3 1 ++ bits 3 7

def problem : CyclicProblem where
  Point := Point
  order := 7
  order_pos := by decide
  zero := infinity
  next := next
  wraps := order_wraps
  distinct := orbit_distinct
  encodePoint := encode
  encode_injective := encode_injective
  parameters := parameters
  outputWidth := 3
  fits := by decide

end Research.SmallCurve
