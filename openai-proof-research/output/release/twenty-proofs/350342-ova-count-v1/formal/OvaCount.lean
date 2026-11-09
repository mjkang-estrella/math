import Mathlib

namespace OvaCount

-- The residue and full-turn frequency used in the source construction.
def residue (p : ℕ) := p % 360
def frequency (p : ℕ) := p / 360

def Eligible (p q r : ℕ) : Prop :=
  0 < r ∧ r < 360 ∧ 
  r ≤ residue p + residue q + 2 ∧
  Nat.Prime (residue p + residue q + 2 - r) ∧
  Nat.Prime (r + 360 * (frequency p + frequency q))
instance (p q r : ℕ) : Decidable (Eligible p q r) := by
  unfold Eligible
  infer_instance

def outputResidues (p q : ℕ) : Finset ℕ :=
  (Finset.range 360).filter (Eligible p q)

def outputPrimes (p q : ℕ) : Finset ℕ :=
  (outputResidues p q).image (fun r => r + 360 * (frequency p + frequency q))

lemma output_prime (p q v : ℕ) (hv : v ∈ outputPrimes p q) : Nat.Prime v := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
  exact ((Finset.mem_filter.mp hr).2).2.2.2.2

lemma decomposition (p q r : ℕ) (hr : Eligible p q r) :
    (residue p + residue q + 2 - r) +
      (r + 360 * (frequency p + frequency q)) = p + q + 2 := by
  have hp := Nat.mod_add_div p 360
  have hq := Nat.mod_add_div q 360
  have hl := hr.2.2.1
  dsimp [residue, frequency] at *
  omega

lemma distinct_output_count (p q : ℕ) :
    (outputPrimes p q).card = (outputResidues p q).card := by
  apply Finset.card_image_of_injective
  intro a b h
  exact Nat.add_right_cancel h

lemma inputs_valid : Nat.Prime 677 ∧ Nat.Prime 401 ∧
    residue 677 = 317 ∧ residue 401 = 41 ∧ frequency 677 = 1 ∧ frequency 401 = 1 := by
  norm_num [residue, frequency]

def witnesses : Finset ℕ :=
  {7,13,23,49,53,67,77,89,91,103,109,119,133,137,161,163,167,187,209,
   221,233,247,251,257,263,271,277,289,293,299,301,313,319,329,331,341,343,349}

lemma witnesses_count : witnesses.card = 38 := by decide

lemma witnesses_eligible (r : ℕ) (hr : r ∈ witnesses) : Eligible 677 401 r := by
  simp only [witnesses, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [Eligible, residue, frequency]

lemma count_lower_bound : 38 ≤ (outputResidues 677 401).card := by
  rw [← witnesses_count]
  apply Finset.card_le_card
  intro r hr
  have h := witnesses_eligible r hr
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.2.1, h⟩

-- The class condition in the original construction is witnessed by the output prime itself.
def PrimeResidue (r : ℕ) : Prop := ∃ v : ℕ, Nat.Prime v ∧ v % 360 = r

lemma residue_class_bridge (p q r : ℕ) (hr : Eligible p q r) : PrimeResidue r := by
  refine ⟨r + 360 * (frequency p + frequency q), hr.2.2.2.2, ?_⟩
  simp only [Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hr.2.1

-- The source explicitly asks for a prime residue class; it is equivalent here.
def SourceEligible (p q r : ℕ) : Prop := PrimeResidue r ∧ Eligible p q r

lemma source_condition_iff (p q r : ℕ) : SourceEligible p q r ↔ Eligible p q r := by
  exact ⟨And.right, fun h => ⟨residue_class_bridge p q r h, h⟩⟩

noncomputable def sourceOutputPrimes (p q : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.range 360).filter (SourceEligible p q)).image
    (fun r => r + 360 * (frequency p + frequency q))

lemma source_outputs_eq (p q : ℕ) : sourceOutputPrimes p q = outputPrimes p q := by
  classical
  simp only [sourceOutputPrimes, source_condition_iff, outputPrimes, outputResidues]

-- Full disproof needs a lower bound; no exhaustive count is assumed.
theorem prime_count_counterexample :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
      38 ≤ (sourceOutputPrimes p q).card ∧ 10 < (sourceOutputPrimes p q).card ∧
      13 < (sourceOutputPrimes p q).card := by
  refine ⟨677, 401, inputs_valid.1, inputs_valid.2.1, ?_⟩
  simp only [source_outputs_eq, distinct_output_count]
  have h := count_lower_bound
  omega
end OvaCount
