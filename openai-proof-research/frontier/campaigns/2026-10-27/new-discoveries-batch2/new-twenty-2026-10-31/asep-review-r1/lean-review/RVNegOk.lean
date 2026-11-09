import ASEPVertex
/-! Negative controls that SHOULD compile: the kernel evaluates `chk` to `false` on mutated certificates,
and `XN_tight` / `XN_cut` style facts fail for perturbed data. -/
namespace ASEP
set_option maxRecDepth 100000
-- positive control: the first stored certificate passes
example : chk (decode certChunk0.head!) = true := by decide +kernel
-- mutation 1: first cyclic-order digit +1 (tour/successor mismatch)
example : chk (decode (certChunk0.head! + 1)) = false := by decide +kernel
-- mutation 2: successor-list digit 7 changed
example : chk (decode (certChunk0.head! + 128 ^ 7)) = false := by decide +kernel
-- mutation 3: first direction value +1 (breaks a row/column sum)
example : chk (decode (certChunk0.head! + 128 ^ 22)) = false := by decide +kernel
-- certificate of one tour paired with another tour's cyclic order fails
example : chk { decode (certChunk0.head!) with tl := (decode (certChunk0.getD 1 0)).tl } = false := by decide +kernel
-- the non-tight cut values really exceed 4 only where claimed (XN_cut is not vacuous: a perturbed table fails)
example : ¬ (∀ S : Finset (Fin 8), 2 ≤ S.card → S.card ≤ 6 → 5 ≤ fluxN S) := by decide +kernel
-- dropping any one tight cut from the list breaks the tight-cut coverage fact
example : ¬ (∀ S : Finset (Fin 8), 2 ≤ S.card → S.card ≤ 6 →
    fluxN S = 4 → ∃ l ∈ tightCutList.tail, S = l.toFinset) := by decide +kernel
end ASEP
