import PartitionSource

namespace KeithMulticolor

/-- All 2300 three-element subsets of the allowed sizes. -/
def triples25 : Finset (Finset ℕ) := (Finset.Icc 1 25).powersetCard 3

def witnessParts (t : Finset ℕ) : Multiset ℕ :=
  let xs := t.sort (· ≤ ·)
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
  let missing := (Finset.Icc 1 25 \ parts.toFinset).sort (· ≤ ·)
  let extra := (parts - parts.dedup).sort (· ≤ ·)
  let a := missing[0]!
  let b := missing[1]!
  let c := extra[0]!
  let d := extra[1]!
  if a < c then {a, c, b} else {c, b, d}

theorem triples25_card : triples25.card = 2300 := by
  norm_num [triples25, Finset.card_powersetCard, Nat.choose]


#print axioms witnessParts
#reduce (witnessParts {1,2,3}).card
#eval (witnessParts {1,2,3}).card
example : (witnessParts {1,2,3}).card = 25 := by decide +kernel
end KeithMulticolor
