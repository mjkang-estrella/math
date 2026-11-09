import Table27
import Table28
import UpperTrees
import LowerIndexed
namespace Schrijver
set_option maxRecDepth 20000
set_option autoImplicit false

def Enumeration27 : Prop := StoredEnumerationComplete 27 12 vertexMasks27.toList
def Enumeration28 : Prop := StoredEnumerationComplete 28 12 vertexMasks28

theorem masks27_valid_at : ∀ i : Fin 819, validMask 27 12 (maskAt27 i.val) = true :=
  table_valid_from_links table27_size maskAt27_lookup vertexMasks27_valid

theorem masks28_valid_at : ∀ i : Fin 3185, validMask 28 12 (maskAt28 i.val) = true :=
  table_valid_from_links table28_size maskAt28_lookup (by simpa using vertexMasks28_valid)

noncomputable def literalIso27 (h : Enumeration27) : indexedGraph 819 maskAt27 ≃g SG 27 12 :=
  indexedLiteralIso maskAt27 masks27_valid_at maskAt27_injective
    (table_coverage_from_links table27_size maskAt27_lookup h)

noncomputable def literalIso28 (h : Enumeration28) : indexedGraph 3185 maskAt28 ≃g SG 28 12 :=
  indexedLiteralIso maskAt28 masks28_valid_at maskAt28_injective
    (table_coverage_from_links table28_size maskAt28_lookup (by simpa [Enumeration28] using h))

def RotationRepresentativeCoverage28 : Prop :=
  ∀ a : Vertex 28 12, ∃ t : Fin 28, ∃ r : Fin 3185,
    r ∈ upperRoots28 ∧ rotateVertex t a = indexedVertex maskAt28 masks28_valid_at r

theorem lower_bridge_from_enumeration (h : Enumeration27) : LowerCertificateBridge := by
  let e := literalIso27 h
  refine ⟨iso_connected e Tree27_000.sound.1, e ⟨29, by decide⟩, e ⟨143, by decide⟩, ?_⟩
  rw [iso_dist e Tree27_000.sound.1]
  exact indexed_distance8

theorem upper_bridge_from_enumeration_rotation (h : Enumeration28)
    (hr : RotationRepresentativeCoverage28) : UpperCertificateBridge := by
  let e := literalIso28 h
  refine ⟨iso_connected e Tree28_000.sound.1, ?_⟩
  let roots : Set (Vertex 28 12) := {v | ∃ r ∈ upperRoots28, e r = v}
  apply orbit_walk_bound roots
  · intro r hr v
    obtain ⟨ri, hri, rfl⟩ := hr
    obtain ⟨vi, rfl⟩ := e.toEquiv.surjective v
    obtain ⟨p, hp⟩ := upperTrees28 ri hri vi
    exact ⟨p.map e.toHom, by simpa using hp⟩
  · intro a
    obtain ⟨t, r, hri, he⟩ := hr a
    refine ⟨rotationIso t, e r, ⟨r, hri, rfl⟩, ?_⟩
    exact he

theorem mathdb_352827_round3_conditional (h27 : Enumeration27) (h28 : Enumeration28)
    (hrot : RotationRepresentativeCoverage28) : ¬ SchrijverUnitGap :=
  mathdb_352827_conditional (lower_bridge_from_enumeration h27)
    (upper_bridge_from_enumeration_rotation h28 hrot)
end Schrijver
