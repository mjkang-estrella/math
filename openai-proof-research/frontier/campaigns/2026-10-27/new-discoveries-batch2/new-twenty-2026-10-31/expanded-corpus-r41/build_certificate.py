import json,pathlib
p=pathlib.Path(__file__).resolve().parent;w=json.loads((p/'leaf-extended-witness.json').read_text());cat=json.loads((p/'leaf-independent.json').read_text())['catalog'];fmt=lambda mask:'{'+','.join(str(i) for i in range(12) if mask>>i&1)+'}' if mask else '∅'
s='''import Mathlib
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LeafCertificate
abbrev V := Fin 12
abbrev E := Fin 12
def ends (e : E) : V × V := !['''+','.join('('+str(a)+','+str(b)+')' for a,b in w['edges'])+'''][e]
def Matching (s : Finset E) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
    (ends i).1 ≠ (ends j).1 ∧ (ends i).1 ≠ (ends j).2 ∧
    (ends i).2 ≠ (ends j).1 ∧ (ends i).2 ≠ (ends j).2
instance (s : Finset E) : Decidable (Matching s) := inferInstanceAs (Decidable (∀ i ∈ s, ∀ j ∈ s, i ≠ j → _))
def catalog : Finset (Finset E) := {'''+','.join(fmt(m) for m in cat)+'''}
def M : Finset E := '''+fmt(w['M'])+'''
def H : Finset E := '''+fmt(w['H'])+'''
def Hp : Finset E := '''+fmt(w['Hp'])+'''
theorem catalog_exact : (Finset.univ.powerset.filter Matching : Finset (Finset E)) = catalog := by decide
theorem matching_iff (s : Finset E) : Matching s ↔ s ∈ catalog := by
  rw [← catalog_exact]
  simp
-- These are certificate-layer claims; graph/path semantic bridges are separate.
theorem maximum_unique : ∀ s ∈ catalog, s.card ≤ 6 ∧ (s.card = 6 → s = M) := by decide
theorem perfect_disjoint_bound : ∀ s ∈ catalog, Disjoint M s → s.card ≤ 3 := by decide
theorem witnesses : Matching M ∧ Matching H ∧ Matching Hp ∧ Disjoint H Hp ∧
    M.card = 6 ∧ H.card = 5 ∧ Hp.card = 5 ∧ (M ∩ (H ∪ Hp)).card = 5 ∧
    (M ∩ H).card = 3 := by decide
end LeafCertificate
'''
(p/'MatchingCertificate.lean').write_text(s)
