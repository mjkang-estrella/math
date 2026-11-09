import Encoding
import Mathlib.Data.Finset.Powerset
namespace Schrijver

-- A reference enumeration with a membership proof, not merely a cardinality count.
-- It is deliberately not asserted to equal either stored certificate table.
noncomputable def referenceSets (n k : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact (Finset.univ.powersetCard k).filter (Stable n)

theorem referenceSets_complete {n k : ℕ} (s : Finset (Fin n)) :
    s ∈ referenceSets n k ↔ s.card = k ∧ Stable n s := by
  classical
  simp [referenceSets]

noncomputable def referenceMasks (n k : ℕ) : Finset ℕ :=
  (referenceSets n k).image encode

theorem referenceMasks_complete {n k m : ℕ} :
    m ∈ referenceMasks n k ↔ validMask n k m = true := by
  classical
  constructor
  · intro hm
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hc, hs⟩ := referenceSets_complete s |>.mp hs
    exact encode_vertex_valid ⟨s, hc, hs⟩
  · intro hm
    have hh := validMask_sound hm
    apply Finset.mem_image.mpr
    refine ⟨decode n m, (referenceSets_complete _).mpr hh.2, encode_decode hh.1⟩

theorem referenceLists_cover {n k : ℕ} (v : Vertex n k) :
    encode v.val ∈ (referenceMasks n k).toList := by
  simpa only [Finset.mem_toList] using
    (referenceMasks_complete.mpr (encode_vertex_valid v))

-- This exact equality is the still-needed link for a stored table.
def StoredEnumerationComplete (n k : ℕ) (table : List ℕ) : Prop :=
  ∀ m, m ∈ table ↔ m ∈ referenceMasks n k

theorem stored_table_covers {n k : ℕ} {table : List ℕ}
    (h : StoredEnumerationComplete n k table) (v : Vertex n k) : encode v.val ∈ table :=
  (h _).mpr (referenceMasks_complete.mpr (encode_vertex_valid v))

end Schrijver
