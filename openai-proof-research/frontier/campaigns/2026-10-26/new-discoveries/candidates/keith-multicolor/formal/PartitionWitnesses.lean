import PartitionSource

namespace KeithMulticolor

/-- All 2300 three-element subsets of the allowed sizes. -/
def triples25 : Finset (Finset ℕ) := (Finset.Icc 1 25).powersetCard 3

/-- Structurally recursive sorting, so closed certificates reduce in the kernel.
The quotient proof establishes independence of the multiset representative. -/
def kernelSort (s : Multiset ℕ) : List ℕ :=
  Quot.liftOn s (List.insertionSort (· ≤ ·)) fun a b h =>
    ((List.perm_insertionSort (· ≤ ·) a).trans
      (h.trans (List.perm_insertionSort (· ≤ ·) b).symm)).eq_of_pairwise'
        (List.pairwise_insertionSort (· ≤ ·) a)
        (List.pairwise_insertionSort (· ≤ ·) b)

def witnessParts (t : Finset ℕ) : Multiset ℕ :=
  let xs := kernelSort t.val
  let u := xs[0]!
  let v := xs[1]!
  let w := xs[2]!
  let d := u + w - v
  if v ≤ d then
    (Finset.Icc 1 25).val - ({u} + {w}) + ({v} + {d})
  else
    (Finset.Icc 1 25).val - ({d} + {v}) + ({u} + {w})

/-- Recover the generating triple from the missing and repeated part sizes. -/
def decodeParts (parts : Multiset ℕ) : Finset ℕ :=
  let missing := kernelSort (Finset.Icc 1 25 \ parts.toFinset).val
  let extra := kernelSort (parts - parts.dedup)
  let a := missing[0]!
  let b := missing[1]!
  let c := extra[0]!
  let d := extra[1]!
  if a < c then {a, c, b} else {c, b, d}

theorem triples25_card : triples25.card = 2300 := by
  norm_num [triples25, Finset.card_powersetCard, Nat.choose]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A fully reduced finite certificate. This checks actual partition multisets
and a left inverse, not merely the numerical coefficient model. -/
theorem witnessParts_certificate : ∀ t ∈ triples25,
    (witnessParts t).card = 25 ∧
    (witnessParts t).sum = 325 ∧
    (witnessParts t).toFinset ⊆ Finset.Icc 1 25 ∧
    (witnessParts t).toFinset.card = 23 ∧
    decodeParts (witnessParts t) = t := by
  decide +kernel

end KeithMulticolor
