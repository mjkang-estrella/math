import Separator
import Mathlib.Data.Fin.VecNotation
namespace Separation
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def coords : Fin 15 → Finset (Fin 5) := ![{0}, {1}, {2}, {3}, {4}, {0,1}, {0,2}, {0,3}, {0,4}, {1,2}, {1,3}, {1,4}, {2,3}, {2,4}, {3,4}]
def decode (m : ℕ) : Point 5 := insert ∅ ((Finset.univ.filter (fun j : Fin 15 => m.testBit j.val)).image coords)
lemma norm6 (f : Point 5 → ℤ) : avg f (decode 6) = avg f (decode 3) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![2,0,1,3,4] i) (by decide)
 have h : rename t (decode 6) = decode 3 := by decide
 rw [← h, avg_rename]
lemma norm29 (f : Point 5 → ℤ) : avg f (decode 29) = avg f (decode 15) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![0,4,1,2,3] i) (by decide)
 have h : rename t (decode 29) = decode 15 := by decide
 rw [← h, avg_rename]
lemma norm119 (f : Point 5 → ℤ) : avg f (decode 119) = avg f (decode 111) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![0,1,2,4,3] i) (by decide)
 have h : rename t (decode 119) = decode 111 := by decide
 rw [← h, avg_rename]
lemma norm518 (f : Point 5 → ℤ) : avg f (decode 518) = avg f (decode 35) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![2,0,1,3,4] i) (by decide)
 have h : rename t (decode 518) = decode 35 := by decide
 rw [← h, avg_rename]
lemma norm526 (f : Point 5 → ℤ) : avg f (decode 526) = avg f (decode 39) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![3,0,1,2,4] i) (by decide)
 have h : rename t (decode 526) = decode 39 := by decide
 rw [← h, avg_rename]
lemma norm527 (f : Point 5 → ℤ) : avg f (decode 527) = avg f (decode 47) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![2,0,1,3,4] i) (by decide)
 have h : rename t (decode 527) = decode 47 := by decide
 rw [← h, avg_rename]
lemma norm559 (f : Point 5 → ℤ) : avg f (decode 559) = avg f (decode 111) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![1,0,2,3,4] i) (by decide)
 have h : rename t (decode 559) = decode 111 := by decide
 rw [← h, avg_rename]
lemma norm2203 (f : Point 5 → ℤ) : avg f (decode 2203) = avg f (decode 655) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![0,1,4,3,2] i) (by decide)
 have h : rename t (decode 2203) = decode 655 := by decide
 rw [← h, avg_rename]
lemma norm3259 (f : Point 5 → ℤ) : avg f (decode 3259) = avg f (decode 751) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![1,0,4,2,3] i) (by decide)
 have h : rename t (decode 3259) = decode 751 := by decide
 rw [← h, avg_rename]
lemma norm5646 (f : Point 5 → ℤ) : avg f (decode 5646) = avg f (decode 615) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![3,0,1,2,4] i) (by decide)
 have h : rename t (decode 5646) = decode 615 := by decide
 rw [← h, avg_rename]
lemma norm5679 (f : Point 5 → ℤ) : avg f (decode 5679) = avg f (decode 751) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![3,0,1,2,4] i) (by decide)
 have h : rename t (decode 5679) = decode 751 := by decide
 rw [← h, avg_rename]
lemma norm5759 (f : Point 5 → ℤ) : avg f (decode 5759) = avg f (decode 1791) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![2,0,1,3,4] i) (by decide)
 have h : rename t (decode 5759) = decode 1791 := by decide
 rw [← h, avg_rename]
lemma norm5775 (f : Point 5 → ℤ) : avg f (decode 5775) = avg f (decode 751) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![3,1,2,0,4] i) (by decide)
 have h : rename t (decode 5775) = decode 751 := by decide
 rw [← h, avg_rename]
lemma norm15327 (f : Point 5 → ℤ) : avg f (decode 15327) = avg f (decode 7167) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![1,3,0,4,2] i) (by decide)
 have h : rename t (decode 15327) = decode 7167 := by decide
 rw [← h, avg_rename]
lemma norm15359 (f : Point 5 → ℤ) : avg f (decode 15359) = avg f (decode 8191) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![0,2,1,4,3] i) (by decide)
 have h : rename t (decode 15359) = decode 8191 := by decide
 rw [← h, avg_rename]
lemma norm28957 (f : Point 5 → ℤ) : avg f (decode 28957) = avg f (decode 751) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![3,4,1,2,0] i) (by decide)
 have h : rename t (decode 28957) = decode 751 := by decide
 rw [← h, avg_rename]
lemma norm30719 (f : Point 5 → ℤ) : avg f (decode 30719) = avg f (decode 16383) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![0,3,1,2,4] i) (by decide)
 have h : rename t (decode 30719) = decode 16383 := by decide
 rw [← h, avg_rename]
lemma norm32286 (f : Point 5 → ℤ) : avg f (decode 32286) = avg f (decode 5871) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![4,0,1,2,3] i) (by decide)
 have h : rename t (decode 32286) = decode 5871 := by decide
 rw [← h, avg_rename]
lemma norm32383 (f : Point 5 → ℤ) : avg f (decode 32383) = avg f (decode 8191) := by
 let t : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i : Fin 5 => ![4,0,1,2,3] i) (by decide)
 have h : rename t (decode 32383) = decode 8191 := by decide
 rw [← h, avg_rename]
theorem no_separator_5_2 : ¬ ∃ f, Separator 5 2 f := by
 rintro ⟨f,hf⟩
 have h0 := avg_submod f hf (decode 8191) (decode 15359) (by unfold allowed; decide) (by unfold allowed; decide)
 have h0a : decode 8191 ∪ decode 15359 = decode 16383 := by decide
 have h0b : decode 8191 ∩ decode 15359 = decode 7167 := by decide
 rw [h0a,h0b] at h0
 simp only [norm15359 f] at h0
 have h1 := avg_submod f hf (decode 15327) (decode 3259) (by unfold allowed; decide) (by unfold allowed; decide)
 have h1a : decode 15327 ∪ decode 3259 = decode 16383 := by decide
 have h1b : decode 15327 ∩ decode 3259 = decode 2203 := by decide
 rw [h1a,h1b] at h1
 simp only [norm2203 f, norm3259 f, norm15327 f] at h1
 have h2 := avg_submod f hf (decode 28957) (decode 1791) (by unfold allowed; decide) (by unfold allowed; decide)
 have h2a : decode 28957 ∪ decode 1791 = decode 30719 := by decide
 have h2b : decode 28957 ∩ decode 1791 = decode 29 := by decide
 rw [h2a,h2b] at h2
 simp only [norm29 f, norm28957 f, norm30719 f] at h2
 have h3 := avg_submod f hf (decode 518) (decode 15) (by unfold allowed; decide) (by unfold allowed; decide)
 have h3a : decode 518 ∪ decode 15 = decode 527 := by decide
 have h3b : decode 518 ∩ decode 15 = decode 6 := by decide
 rw [h3a,h3b] at h3
 simp only [norm6 f, norm518 f, norm527 f] at h3
 have h4 := avg_submod f hf (decode 518) (decode 47) (by unfold allowed; decide) (by unfold allowed; decide)
 have h4a : decode 518 ∪ decode 47 = decode 559 := by decide
 have h4b : decode 518 ∩ decode 47 = decode 6 := by decide
 rw [h4a,h4b] at h4
 simp only [norm6 f, norm518 f, norm559 f] at h4
 have h5 := avg_submod f hf (decode 5646) (decode 39) (by unfold allowed; decide) (by unfold allowed; decide)
 have h5a : decode 5646 ∪ decode 39 = decode 5679 := by decide
 have h5b : decode 5646 ∩ decode 39 = decode 6 := by decide
 rw [h5a,h5b] at h5
 simp only [norm6 f, norm5646 f, norm5679 f] at h5
 have h6 := avg_submod f hf (decode 5646) (decode 119) (by unfold allowed; decide) (by unfold allowed; decide)
 have h6a : decode 5646 ∪ decode 119 = decode 5759 := by decide
 have h6b : decode 5646 ∩ decode 119 = decode 6 := by decide
 rw [h6a,h6b] at h6
 simp only [norm6 f, norm119 f, norm5646 f, norm5759 f] at h6
 have h7 := avg_submod f hf (decode 5646) (decode 655) (by unfold allowed; decide) (by unfold allowed; decide)
 have h7a : decode 5646 ∪ decode 655 = decode 5775 := by decide
 have h7b : decode 5646 ∩ decode 655 = decode 526 := by decide
 rw [h7a,h7b] at h7
 simp only [norm526 f, norm5646 f, norm5775 f] at h7
 have h8 := avg_submod f hf (decode 32286) (decode 615) (by unfold allowed; decide) (by unfold allowed; decide)
 have h8a : decode 32286 ∪ decode 615 = decode 32383 := by decide
 have h8b : decode 32286 ∩ decode 615 = decode 518 := by decide
 rw [h8a,h8b] at h8
 simp only [norm518 f, norm32286 f, norm32383 f] at h8
 have h9 := avg_bad f hf (decode 3) (by unfold allowed; decide) (by decide)
 have h10 := avg_good f hf ({0,1,2} : Finset (Fin 5))
 have h10a : phi 2 ({0,1,2} : Finset (Fin 5)) = decode 615 := by decide
 rw [h10a] at h10
 have h11 := avg_good f hf ({0,1,2,3} : Finset (Fin 5))
 have h11a : phi 2 ({0,1,2,3} : Finset (Fin 5)) = decode 5871 := by decide
 rw [h11a] at h11
 have h12 := avg_bad f hf (decode 16383) (by unfold allowed; decide) (by decide)
 have hc : (Fintype.card (Equiv.Perm (Fin 5)) : ℤ) = 120 := by decide
 rw [hc] at h10 h11
 linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem source_existence_refuted : ¬ SeparationExistence := by
 intro h
 exact no_separator_5_2 (h 5 2 (by decide))
#print axioms source_existence_refuted
end Separation
