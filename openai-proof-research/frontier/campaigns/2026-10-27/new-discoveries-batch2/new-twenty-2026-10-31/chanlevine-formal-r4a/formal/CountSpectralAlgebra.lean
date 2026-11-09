import CountTransfer
namespace ChanLevine.Round3
open scoped Matrix

/-- Ordered product; meaningful also for noncommutative matrices. -/
def orderedProduct {M : Type*} [Monoid M] (f : ℕ → M) (n : ℕ) : M :=
  Nat.rec 1 (fun r a => a * f r) n

@[simp] theorem orderedProduct_zero {M : Type*} [Monoid M] (f : ℕ → M) :
    orderedProduct f 0 = 1 := rfl

@[simp] theorem orderedProduct_succ {M : Type*} [Monoid M] (f : ℕ → M) (r : ℕ) :
    orderedProduct f (r+1) = orderedProduct f r * f r := rfl

theorem orderedProduct_add {M : Type*} [Monoid M] (f : ℕ → M) (a b : ℕ) :
    orderedProduct f (a+b) = orderedProduct f a * orderedProduct (fun k => f (a+k)) b := by
  induction b with
  | zero => simp
  | succ b ih =>
    change orderedProduct f ((a+b)+1) = _
    rw [orderedProduct_succ, ih, orderedProduct_succ, mul_assoc]

theorem periodic_multiple {M : Type*} (f : ℕ → M) (e : ℕ)
    (h : ∀ k, f (e+k) = f k) (r k : ℕ) : f (e*r+k) = f k := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.mul_succ]
    calc
      f (e*r+e+k) = f (e+(e*r+k)) := by congr 1; omega
      _ = f (e*r+k) := h _
      _ = f k := ih

theorem orderedProduct_period {M : Type*} [Monoid M] (f : ℕ → M) (e : ℕ)
    (h : ∀ k, f (e+k) = f k) (r : ℕ) :
    orderedProduct f (e*r) = orderedProduct f e ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.mul_succ, orderedProduct_add, ih]
    have hf : (fun k => f (e*r+k)) = f := funext (periodic_multiple f e h r)
    rw [hf, pow_succ]

variable {R : Type*} [CommRing R]

def lucasState (p d : R) (r : ℕ) : R × R :=
  Nat.rec (2,p) (fun _ s => (s.2, p*s.2-d*s.1)) r

def lucasTrace (p d : R) (r : ℕ) : R := (lucasState p d r).1

theorem lucasTrace_zero (p d : R) : lucasTrace p d 0 = 2 := rfl

theorem lucasTrace_one (p d : R) : lucasTrace p d 1 = p := rfl

theorem lucasTrace_next (p d : R) (r : ℕ) :
    lucasTrace p d (r+2) = p * lucasTrace p d (r+1) - d * lucasTrace p d r := rfl

theorem trace_pow_eq_lucas (P : Matrix (Fin 2) (Fin 2) R) (r : ℕ) :
    (P^r).trace = lucasTrace P.trace P.det r := by
  induction r using Nat.twoStepInduction with
  | zero => simp [lucasTrace_zero, Matrix.trace]
  | one => simp [lucasTrace_one]
  | more r ih ih' => rw [two_lucas_trace, ih, ih', lucasTrace_next]

theorem trace_pow_eq_of_trace_det (P Q : Matrix (Fin 2) (Fin 2) R)
    (hp : P.trace = Q.trace) (hd : P.det = Q.det) (r : ℕ) :
    (P^r).trace = (Q^r).trace := by
  rw [trace_pow_eq_lucas, trace_pow_eq_lucas, hp, hd]

theorem domino_trace (z g : R) : (dominoMatrix z g).trace = 1+z := by
  simp [Matrix.trace, Matrix.diag, dominoMatrix, Fin.sum_univ_two]

/-- The constant transfer matrix has eigenvalues 1 and z, without diagonalization. -/
theorem constant_domino_trace (z : R) (r : ℕ) :
    ((dominoMatrix z 1)^r).trace = 1 + z^r := by
  induction r using Nat.twoStepInduction with
  | zero => simp only [pow_zero, Matrix.trace_one, Fintype.card_fin]; ring
  | one => simpa using domino_trace z (1 : R)
  | more r ih ih' =>
    rw [two_lucas_trace, ih, ih', domino_det, domino_trace]
    simp only [one_pow, mul_one, pow_succ]
    ring
end ChanLevine.Round3
