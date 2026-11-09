from pathlib import Path
p=Path('General.lean');s=p.read_text();i=s.index('/-- `w`');s=s[:i]+'''/-- Closed neighbourhood of a vertex, as a predicate on vertices. -/
def ClosedNbr (G : SimpleGraph V) (v w : V) : Prop := w = v ∨ G.Adj v w

/-- Closed neighbourhood of a vertex set. -/
def ClosedNbrSet (G : SimpleGraph V) (D : Finset V) (w : V) : Prop :=
  ∃ v ∈ D, ClosedNbr G v w

'''+s[i:];i=s.index('/-- `D` is irredundant');s=s[:i]+'''lemma privateNbr_closed (G : SimpleGraph V) (D : Finset V) (v w : V) :
    IsPrivateNbr G D v w ↔ ClosedNbr G v w ∧ ¬ ClosedNbrSet G (D.erase v) w := by
  simp only [IsPrivateNbr, ClosedNbr, ClosedNbrSet, Finset.mem_erase]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h, fun ⟨u, ⟨hne, hu⟩, hw⟩ => hn u hu hne hw⟩
  · rintro ⟨h, hn⟩
    exact ⟨h, fun u hu hne hw => hn ⟨u, ⟨hne, hu⟩, hw⟩⟩

'''+s[i:];p.write_text(s)
p=Path('Endpoint.lean');s=p.read_text();i=s.index('/-- Finite check (c)');s=s[:i]+'''theorem ir_G9 : IR G9 = 3 := by
  obtain ⟨D, hD, hc⟩ := ir_attained G9
  apply le_antisymm
  · exact hc ▸ irredundant_card_le hD
  · have h := ir_upper (walk_irredundant 0)
    rwa [walk_card] at h

'''+s[i:];s=s.replace('def pathIso','noncomputable def pathIso');p.write_text(s)
