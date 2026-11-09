import PolynexusGapCount
import Mathlib.Tactic.LinearCombination

/-- Polynomial summation by induction, in characteristic zero. -/
theorem PInner (m : ℕ) (c : ℚ) :
    12 * (∑ k ∈ Finset.range m, ((k:ℚ)+1)*((k:ℚ)+2)*(c+k)) =
      (m:ℚ)*(m+1)*(m+2)*(4*c+3*m-3) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    push_cast
    linear_combination ih

def PA (m : ℚ) : ℚ := m*(m+1)^2*(m+2)
def PQ (n : ℚ) : ℚ := n*(n-1)*(n+1)*(n+2)*(19*n^2+19*n+6)

theorem PQuartic (n : ℕ) :
    10*(∑ m ∈ Finset.range n, PA m) = (n:ℚ)*(n-1)*(n+1)*(n+2)*(2*n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    dsimp [PA] at *
    linear_combination ih

theorem POuter (n : ℕ) :
    30*(∑ m ∈ Finset.range n, PA m*(4*n-m+1)) = PQ n := by
  induction n with
  | zero => simp [PQ]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hs : (∑ m ∈ Finset.range n, PA m*(4*(n+1:ℕ)-m+1)) =
        (∑ m ∈ Finset.range n, PA m*(4*n-m+1)) +
        4*(∑ m ∈ Finset.range n, PA m) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      push_cast
      ring
    rw [hs]
    have hq := PQuartic n
    push_cast
    dsimp [PA, PQ] at *
    linear_combination ih + 12*hq

/-- Reindex the actual length fibers by reversed remaining lengths and gaps.
All natural subtractions here have explicit bounds; the polynomial work
is performed only after the genuine cardinality identity. -/
theorem PDouble (n : ℕ) :
    2*((PLeftM n).card : ℚ) =
      ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m,
        ((k:ℚ)+1)*(k+2)*(m+1)*(n-m+k+1) := by
  rw [PLeftM_card_sum]
  push_cast
  rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => (⟨n-p.1-1,n-p.1-p.2-2⟩ : Sigma fun _ : ℕ => ℕ))
  · intro p hp
    have h := PLengths_mem.1 hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro p hp q hq he
    have h1 := PLengths_mem.1 hp
    have h2 := PLengths_mem.1 hq
    have hm : n-p.1-1 = n-q.1-1 := congrArg Sigma.fst he
    have hk : n-p.1-p.2-2 = n-q.1-q.2-2 := by
      exact congrArg (fun s : Sigma fun _ : ℕ => ℕ => s.2) he
    apply Prod.ext <;> omega
  · intro s hs
    have hm := (Finset.mem_sigma.1 hs).1
    have hk := (Finset.mem_sigma.1 hs).2
    have hm' := Finset.mem_range.1 hm
    have hk' := Finset.mem_range.1 hk
    refine ⟨(n-s.1-1,s.1-s.2-1), PLengths_mem.2 (by dsimp; omega), ?_⟩
    have h1 : n-(n-s.1-1)-1 = s.1 := by omega
    have h2 : n-(n-s.1-1)-(s.1-s.2-1)-2 = s.2 := by omega
    simp only [h1,h2]
  · intro p hp
    have h := PLengths_mem.1 hp
    have h1 : n-p.1 = n-p.1-1+1 := by omega
    have h2 : n-p.2 = n-(n-p.1-1)+(n-p.1-p.2-2)+1 := by omega
    have hc := PGT_card (n-p.1-p.2-2)
    have hcQ : 2*((PGT (n-p.1-p.2-2)).card : ℚ) =
        (((n-p.1-p.2-2:ℕ):ℚ)+1) * (((n-p.1-p.2-2:ℕ):ℚ)+2) := by
      exact_mod_cast hc
    have h1Q : ((n-p.1:ℕ):ℚ) = ((n-p.1-1:ℕ):ℚ)+1 := by exact_mod_cast h1
    have h2Q : ((n-p.2:ℕ):ℚ) = (n:ℚ)-((n-p.1-1:ℕ):ℚ)+((n-p.1-p.2-2:ℕ):ℚ)+1 := by
      rw [h2]
      push_cast
      rw [Nat.cast_sub (show n-p.1-1 ≤ n by omega)]
    dsimp
    rw [h1Q,h2Q]
    linear_combination (((n-p.1-1:ℕ):ℚ)+1)*
      ((n:ℚ)-((n-p.1-1:ℕ):ℚ)+((n-p.1-p.2-2:ℕ):ℚ)+1)*hcQ

/-- Exact evaluation of the finite zero-pair convolution by two telescoping
polynomial identities. No power-series or evaluated-sum assumption. -/
theorem PLeft_eval (n : ℕ) : 720*((PLeftM n).card : ℚ) = PQ n := by
  have hd := PDouble n
  have hs : 12*(∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m,
        ((k:ℚ)+1)*(k+2)*(m+1)*(n-m+k+1)) =
      ∑ m ∈ Finset.range n, PA m*(4*n-m+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hi := PInner m ((n:ℚ)-m+1)
    have hr : (∑ k ∈ Finset.range m, ((k:ℚ)+1)*(k+2)*(m+1)*(n-m+k+1)) =
        (m+1:ℚ)*(∑ k ∈ Finset.range m, ((k:ℚ)+1)*(k+2)*((n:ℚ)-m+1+k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hr]
    dsimp [PA]
    linear_combination (m+1:ℚ)*hi
  have ho := POuter n
  linear_combination 360*hd + 30*hs + ho

/-- Literal positive-n Polynexus formula for the already defined cardinality
of actual ordered nonzero matrix operands with ordinary nonzero product.
The proof also establishes the harmless empty-size extension. -/
theorem polynexus_rational (n : ℕ) :
    120*(psi n : ℚ) = (n+1:ℚ)^7-(n:ℚ)^7-(n+1:ℚ)^3+(n:ℚ)^3 := by
  have hp : (psi n:ℚ)+2*((PLeftM n).card:ℚ) = ((PNZ n).card:ℚ)^2 := by
    exact_mod_cast partition_card n
  have ht : 6*((PNZ n).card:ℚ) = (n:ℚ)*(n+1)*(2*n+1) := by
    exact_mod_cast PNZ_card_sq n
  have hd := PLeft_eval n
  dsimp [PQ] at hd
  have ht2 : 36*((PNZ n).card:ℚ)^2 = ((n:ℚ)*(n+1)*(2*n+1))^2 := by
    linear_combination (6*((PNZ n).card:ℚ)+(n:ℚ)*(n+1)*(2*n+1))*ht
  linear_combination 120*hp + (10/3:ℚ)*ht2 - (1/3:ℚ)*hd

theorem polynexus_integer (n : ℕ) :
    120*(psi n : ℤ) = (n+1:ℤ)^7-(n:ℤ)^7-(n+1:ℤ)^3+(n:ℤ)^3 := by
  exact_mod_cast polynexus_rational n

theorem polynexus_positive (n : ℕ) (_hn : 0 < n) :
    (psi n : ℚ) = ((n+1:ℚ)^7-(n:ℚ)^7-(n+1:ℚ)^3+(n:ℚ)^3)/120 := by
  have h := polynexus_rational n
  linear_combination (1/120:ℚ)*h
