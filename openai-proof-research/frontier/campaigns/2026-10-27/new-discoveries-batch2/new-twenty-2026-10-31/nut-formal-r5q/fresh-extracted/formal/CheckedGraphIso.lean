import GraphChecker
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.List.Nodup
namespace Nut8
/-- The bounded lookup in a checked permutation never uses its default. -/
def checkedVertex {n : ℕ} (p : List ℕ) (hp : p.Perm (List.range n))
    (i : Fin n) : Fin n :=
  have hl : p.length = n := by simpa using hp.length_eq
  ⟨p[i.val]' (by omega), by
    have hm : p[i.val] ∈ p := List.getElem_mem (by omega)
    exact List.mem_range.mp (hp.mem_iff.mp hm)⟩

lemma checkedVertex_bijective {n : ℕ} (p : List ℕ) (hp : p.Perm (List.range n)) :
    Function.Bijective (checkedVertex p hp) := by
  have hl : p.length = n := by simpa using hp.length_eq
  have hd : p.Nodup := hp.nodup_iff.mpr List.nodup_range
  have hi : Function.Injective (checkedVertex p hp) := by
    intro i j he
    have he' : p[i.val] = p[j.val] := congrArg Fin.val he
    have he'' : (⟨i.val, by omega⟩ : Fin p.length) = ⟨j.val, by omega⟩ :=
      hd.injective_get he'
    exact Fin.ext (congrArg (fun x : Fin p.length => x.val) he'')
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hi, rfl⟩

noncomputable def checkedEquiv {n : ℕ} (p : List ℕ)
    (hp : p.Perm (List.range n)) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (checkedVertex p hp) (checkedVertex_bijective p hp)

lemma checkedVertex_lookup {n : ℕ} (p : List ℕ) (hp : p.Perm (List.range n))
    (i : Fin n) : (checkedEquiv p hp i).val = p[i.val]?.getD n := by
  have hl : p.length = n := by simpa using hp.length_eq
  simp [checkedEquiv, Equiv.ofBijective, checkedVertex, show i.val < p.length by omega]

/-- Converts a successful list checker into an actual graph isomorphism.
The hypotheses merely identify the two input graph adjacency relations. -/
noncomputable def graphIsoCheck_equiv {n a b : ℕ} (p : List ℕ)
    (hc : graphIsoCheck n a b p = true)
    (A B : SimpleGraph (Fin n))
    (ha : ∀ i j, A.Adj i j ↔ graphBit n a i.val j.val = true)
    (hb : ∀ i j, B.Adj i j ↔ graphBit n b i.val j.val = true) : B ≃g A where
  toEquiv := checkedEquiv p (graphIsoCheck_sound n a b p hc).1
  map_rel_iff' := by
    intro i j
    rw [ha, hb]
    rw [checkedVertex_lookup, checkedVertex_lookup]
    rw [(graphIsoCheck_sound n a b p hc).2 i.val (List.mem_range.mpr i.isLt)
      j.val (List.mem_range.mpr j.isLt)]
/-- A checked extension yields an actual isomorphism into one of the listed graphs.
No assertion of universal catalogue coverage is used here. -/
theorem extensionClosed_equiv {n a mask : ℕ} (targets : List ℕ)
    (cs : List (ℕ × ℕ × List ℕ))
    (hc : extensionClosed n a targets cs = true)
    (hm : mask ∈ List.range (2^n)) (he : eligibleNeighbors n a mask = true)
    (A : SimpleGraph (Fin (n+1))) (B : ℕ → SimpleGraph (Fin (n+1)))
    (ha : ∀ i j, A.Adj i j ↔ graphBit (n+1) (extendGraph n a mask) i.val j.val = true)
    (hb : ∀ b ∈ targets, ∀ i j, (B b).Adj i j ↔ graphBit (n+1) b i.val j.val = true) :
    ∃ b ∈ targets, Nonempty (B b ≃g A) := by
  obtain ⟨c, _, _, ht, hi⟩ := extensionClosed_sound n a targets cs hc mask hm he
  exact ⟨c.2.1, ht, ⟨graphIsoCheck_equiv c.2.2 hi A (B c.2.1) ha (hb _ ht)⟩⟩
end Nut8
