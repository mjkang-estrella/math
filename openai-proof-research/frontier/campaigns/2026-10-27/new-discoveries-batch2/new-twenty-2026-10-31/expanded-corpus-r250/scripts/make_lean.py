import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];o=json.loads((D/'matroid-certificate.json').read_text())
f=lambda xs:'{'+', '.join(map(str,xs))+'}'
s='''import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finset.Powerset

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371
abbrev V := Fin 9

def bases : Finset (Finset V) := {\n'''+',\n'.join(f(b) for b in o['bases'])+'''}

def BP (B : Set V) : Prop := ∃ b ∈ bases, (b : Set V) = B

theorem exchange_checked : ∀ a ∈ bases, ∀ b ∈ bases,
    ∀ e ∈ a \\ b, ∃ f ∈ b \\ a, insert f (a.erase e) ∈ bases := by decide

theorem exchange : ExchangeProperty BP := by
  rintro A B ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ e he
  obtain ⟨f, hf, h⟩ := exchange_checked a ha b hb e (by simpa using he)
  refine ⟨f, by simpa using hf, insert f (a.erase e), h, ?_⟩
  ext x
  simp

noncomputable def M : Matroid V := Matroid.ofIsBaseOfFinite
  (Set.finite_univ) BP
  ⟨({0,2,3,5} : Finset V), by exact ⟨{0,2,3,5}, by decide, rfl⟩⟩
  exchange (by intro B _; exact Set.subset_univ B)

end CommonBasis332371
'''
(D/'lean/Endpoint.lean').write_text(s)
