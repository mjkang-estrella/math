import Mathlib.Algebra.MvPolynomial.CommRing
import CrownVAlg
import CrownVRankOneMap

/-!
# CrownV one-swap monomial certificate in the original polynomial ring

The actual finite product over the UNCHANGED polynomial ring
`CrownV.PolyRing n K = MvPolynomial (V n × Bool) K` with the UNCHANGED
variables `CrownV.xx` / `CrownV.yy`:

`M d a = ∏ v : V n, xx v ^ a v * yy v ^ (d v - a v)`,

for arbitrary allocations `d a : V n → ℕ`.  For the genuine vertex-indexed
double update `vswapAlloc a i j` (a fresh name; the sealed Nat-indexed
`swapAlloc` of r24 is not shadowed) and every pair `i ≠ j` with capacity
`a v ≤ d v`, room `a i < d i` and positivity `0 < a j`, an explicit polynomial
`q` (a finite product of the other factors, with one sign) satisfies

`M d a - M d (vswapAlloc a i j) = q * minor i j`.

Pure commutative-ring algebra: no evaluation, no division, no field / domain /
characteristic / nontriviality assumption, no graph-adjacency premise.  The
case `n = 0` is covered by the same universally quantified statement.

Not claimed here (still unpaid): the Nat-prefix-to-vertex bridge to r27,
multi-swap telescoping, membership in the original graph-edge ideal `J` for
arbitrary pairs (only the unchanged all-pair ideal `allPairMinorIdeal` of
`CrownVRankOneMap` appears, as a corollary), and any reverse-kernel statement.
-/

namespace CrownV

/-- One factor of `x` moved out of a positive exponent. -/
theorem pow_pred {M : Type*} [Monoid M] {m : ℕ} (hm : 0 < m) (x : M) :
    x ^ m = x ^ (m - 1) * x := by
  obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [hj, pow_succ, Nat.add_sub_cancel]

/-- The vertex-indexed allocation after the legal swap `j → i`: the plain
function `a` with two ordinary function updates, `+1` at vertex `i` and `-1`
at vertex `j`. -/
def vswapAlloc {n : ℕ} (a : V n → ℕ) (i j : V n) : V n → ℕ :=
  Function.update (Function.update a i (a i + 1)) j (a j - 1)

/-- Pointwise reading of the two vertex updates. -/
theorem vswapAlloc_apply {n : ℕ} (a : V n → ℕ) (i j v : V n) :
    vswapAlloc a i j v
      = if v = j then a j - 1 else if v = i then a i + 1 else a v := by
  show Function.update (Function.update a i (a i + 1)) j (a j - 1) v
      = (if v = j then a j - 1 else if v = i then a i + 1 else a v)
  rw [Function.update_apply, Function.update_apply]

/-- One unit gained at the receiving vertex `i`. -/
theorem vswapAlloc_at_i {n : ℕ} (a : V n → ℕ) (i j : V n) (hne : i ≠ j) :
    vswapAlloc a i j i = a i + 1 := by
  show Function.update (Function.update a i (a i + 1)) j (a j - 1) i = a i + 1
  rw [Function.update_apply, Function.update_apply, if_neg hne, if_pos (rfl : i = i)]

/-- One unit lost at the losing vertex `j`. -/
theorem vswapAlloc_at_j {n : ℕ} (a : V n → ℕ) (i j : V n) :
    vswapAlloc a i j j = a j - 1 := by
  show Function.update (Function.update a i (a i + 1)) j (a j - 1) j = a j - 1
  rw [Function.update_apply, if_pos (rfl : j = j)]

/-- Unchanged away from the two vertices. -/
theorem vswapAlloc_else {n : ℕ} (a : V n → ℕ) (i j v : V n) (hi : v ≠ i) (hj : v ≠ j) :
    vswapAlloc a i j v = a v := by
  show Function.update (Function.update a i (a i + 1)) j (a j - 1) v = a v
  rw [Function.update_apply, if_neg hj, Function.update_apply, if_neg hi]

section MonomialCertificate

variable {n : ℕ} {K : Type*} [CommRing K]

/-- The monomial factor of the allocation product at vertex `v`. -/
noncomputable def vmono (d a : V n → ℕ) (v : V n) : PolyRing n K :=
  xx v ^ a v * yy v ^ (d v - a v)

theorem vmono_def {d a : V n → ℕ} {v : V n} :
    vmono d a v = xx v ^ a v * yy v ^ (d v - a v) := rfl

/-- The actual finite allocation product `M d a = ∏ v, xx v ^ a v * yy v ^ (d v - a v)`. -/
noncomputable def vswapProd (d a : V n → ℕ) : PolyRing n K :=
  (Finset.univ : Finset (V n)).prod (vmono d a)

theorem vswapProd_def {d a : V n → ℕ} :
    vswapProd d a = (Finset.univ : Finset (V n)).prod (vmono d a) := rfl

/-- A product over all vertices splits off any two distinct vertices. -/
theorem prod_univ_erase_two (f : V n → PolyRing n K) (i j : V n) (hij : i ≠ j) :
    (Finset.univ : Finset (V n)).prod f
      = f i * f j * (((Finset.univ : Finset (V n)).erase i).erase j).prod f := by
  have hji : j ∈ (Finset.univ : Finset (V n)).erase i := by
    refine Finset.mem_erase.2 ⟨?_, ?_⟩
    · intro hh
      exact hij hh.symm
    · exact Finset.mem_univ j
  have hi : i ∈ (Finset.univ : Finset (V n)) := Finset.mem_univ i
  calc (Finset.univ : Finset (V n)).prod f
      = (insert i ((Finset.univ : Finset (V n)).erase i)).prod f := by
        rw [Finset.insert_erase hi]
    _ = f i * ((Finset.univ : Finset (V n)).erase i).prod f := by
        rw [Finset.prod_insert
          (Finset.not_mem_erase : i ∉ (Finset.univ : Finset (V n)).erase i)]
    _ = f i * (insert j (((Finset.univ : Finset (V n)).erase i).erase j)).prod f := by
        rw [Finset.insert_erase hji]
    _ = f i * (f j * (((Finset.univ : Finset (V n)).erase i).erase j).prod f) := by
        rw [Finset.prod_insert
          (Finset.not_mem_erase : j ∉ ((Finset.univ : Finset (V n)).erase i).erase j)]
    _ = f i * f j * (((Finset.univ : Finset (V n)).erase i).erase j).prod f := by
        ring

/-- With room `a i < d i`, the `a`-monomial at `i` is the common factor times
one `y_i`. -/
theorem vmono_a_i (d a : V n → ℕ) (i : V n) (hlt : a i < d i) :
    vmono d a i = (xx i ^ a i * yy i ^ (d i - a i - 1)) * yy i := by
  have h1 : 0 < d i - a i := by omega
  rw [vmono_def, pow_pred h1 (yy i)]
  ring

/-- The swapped monomial at `i` is the same common factor times one `x_i`. -/
theorem vmono_b_i (d a : V n → ℕ) (i j : V n) (hne : i ≠ j) :
    vmono d (vswapAlloc a i j) i
      = (xx i ^ a i * yy i ^ (d i - a i - 1)) * xx i := by
  have h1 : d i - (a i + 1) = d i - a i - 1 := by omega
  rw [vmono_def, vswapAlloc_at_i a i j hne, pow_succ, h1]
  ring

/-- With positivity `0 < a j`, the `a`-monomial at `j` is the common factor
times one `x_j`. -/
theorem vmono_a_j (d a : V n → ℕ) (j : V n) (hpos : 0 < a j) :
    vmono d a j = (xx j ^ (a j - 1) * yy j ^ (d j - a j)) * xx j := by
  rw [vmono_def, pow_pred hpos (xx j)]
  ring

/-- With capacity at `j`, the swapped monomial at `j` is the same common
factor times one `y_j`. -/
theorem vmono_b_j (d a : V n → ℕ) (i j : V n) (hc : a j ≤ d j) (hpos : 0 < a j) :
    vmono d (vswapAlloc a i j) j
      = (xx j ^ (a j - 1) * yy j ^ (d j - a j)) * yy j := by
  have h1 : d j - (a j - 1) = d j - a j + 1 := by omega
  rw [vmono_def, vswapAlloc_at_j a i j, h1, pow_succ]
  ring

/-- The one-swap monomial certificate: an explicit polynomial `q` (the finite
product of all unaffected factors, one sign) with
`M d a - M d (vswapAlloc a i j) = q * minor i j`. -/
theorem exists_vswap_monomial_certificate (d a : V n → ℕ) (i j : V n) (hij : i ≠ j)
    (hcap : ∀ v : V n, a v ≤ d v) (hlt : a i < d i) (hpos : 0 < a j) :
    ∃ q : PolyRing n K,
      vswapProd d a - vswapProd d (vswapAlloc a i j) = q * minor i j := by
  have hminor : minor i j = xx i * yy j - xx j * yy i := rfl
  have hPcongr : (((Finset.univ : Finset (V n)).erase i).erase j).prod
        (vmono d (vswapAlloc a i j))
      = (((Finset.univ : Finset (V n)).erase i).erase j).prod (vmono d a) := by
    refine Finset.prod_congr ?_
    intro x hx
    have hxj : x ≠ j := hx.1
    have hxi : x ≠ i := (Finset.mem_erase.1 hx.2).1
    rw [vmono_def, vmono_def, vswapAlloc_else a i j x hxi hxj]
  have hA : vswapProd d a
      = (xx i ^ a i * yy i ^ (d i - a i - 1) * yy i)
        * (xx j ^ (a j - 1) * yy j ^ (d j - a j) * xx j)
        * (((Finset.univ : Finset (V n)).erase i).erase j).prod (vmono d a) := by
    rw [vswapProd_def, prod_univ_erase_two (vmono d a) i j hij,
      vmono_a_i d a i hlt, vmono_a_j d a j hpos]
  have hB : vswapProd d (vswapAlloc a i j)
      = (xx i ^ a i * yy i ^ (d i - a i - 1) * xx i)
        * (xx j ^ (a j - 1) * yy j ^ (d j - a j) * yy j)
        * (((Finset.univ : Finset (V n)).erase i).erase j).prod (vmono d a) := by
    have hc : a j ≤ d j := hcap j
    rw [vswapProd_def, prod_univ_erase_two (vmono d (vswapAlloc a i j)) i j hij,
      vmono_b_i d a i j hne, vmono_b_j d a i j hc hpos, hPcongr]
  refine ⟨-(xx i ^ a i * yy i ^ (d i - a i - 1)
    * ((xx j ^ (a j - 1) * yy j ^ (d j - a j))
    * (((Finset.univ : Finset (V n)).erase i).erase j).prod (vmono d a))), ?_⟩
  rw [hA, hB, hminor]
  ring

/-- Corollary: the one-swap monomial difference lies in the unchanged
all-pair minor ideal (not the original graph-edge ideal `J`). -/
theorem vswap_diff_mem_allPairMinorIdeal (d a : V n → ℕ) (i j : V n) (hij : i ≠ j)
    (hcap : ∀ v : V n, a v ≤ d v) (hlt : a i < d i) (hpos : 0 < a j) :
    vswapProd d a - vswapProd d (vswapAlloc a i j)
      ∈ allPairMinorIdeal (n := n) (K := K) := by
  obtain ⟨q, hq⟩ := exists_vswap_monomial_certificate d a i j hij hcap hlt hpos
  have h1 : (minor i j : PolyRing n K) ∈ allPairMinorIdeal (n := n) (K := K) :=
    minor_mem_allPairMinorIdeal i j
  have h2 : q • (minor i j : PolyRing n K) ∈ allPairMinorIdeal (n := n) (K := K) :=
    Submodule.smul_mem _ q h1
  rw [smul_eq_mul] at h2
  rw [hq]
  exact h2

end MonomialCertificate

end CrownV
