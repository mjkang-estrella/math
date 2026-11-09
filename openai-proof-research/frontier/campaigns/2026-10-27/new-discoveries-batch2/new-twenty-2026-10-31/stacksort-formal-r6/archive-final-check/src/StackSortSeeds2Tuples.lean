import StackSortSeeds2Words

namespace StackSort.Seeds2

/-- All decompositions of a fixed word into exactly r nonempty consecutive words. -/
def sections (r : ℕ) (w : List ℕ) : Finset (List (List ℕ)) :=
  Nat.rec (fun w => if w = [] then {[]} else ∅)
    (fun _ rec w => (Finset.Icc 1 w.length).biUnion fun k =>
      (rec (w.drop k)).image (fun F => w.take k :: F)) r w

 theorem sections_zero (w : List ℕ) : sections 0 w = (if w = [] then {[]} else ∅) := rfl
 theorem sections_succ (r : ℕ) (w : List ℕ) : sections (r+1) w =
   (Finset.Icc 1 w.length).biUnion (fun k => (sections r (w.drop k)).image (fun F => w.take k :: F)) := rfl

def tuples (M r : ℕ) : Finset (List (List ℕ)) :=
  (words M).biUnion (sections r)

def output (F : List (List ℕ)) : List ℕ := (F.map s).flatten

def XI (M r t : ℕ) : ℕ :=
  ((tuples M r ×ˢ tuples M t).filter (fun p => output p.1 = output p.2)).card

 theorem mem_sections {r : ℕ} {w : List ℕ} {F : List (List ℕ)} :
    F ∈ sections r w ↔ F.length = r ∧ F.flatten = w ∧ ∀ u ∈ F, u ≠ [] := by
  induction r generalizing w F with
  | zero =>
    simp only [sections_zero]
    split_ifs with h
    · subst w; simp only [Finset.mem_singleton, List.length_eq_zero_iff]; constructor
      · rintro rfl; simp
      · rintro ⟨rfl, _, _⟩; rfl
    · simp only [Finset.notMem_empty, false_iff]
      rintro ⟨hl, he, _⟩
      have : F = [] := List.length_eq_zero_iff.mp hl
      simp_all
  | succ r ih =>
    simp only [sections_succ, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨k, ⟨hk, hkw⟩, G, hG, rfl⟩
      rcases ih.mp hG with ⟨hGl, hGw, hGn⟩
      refine ⟨by simp [hGl], by simp [hGw], ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · intro he
        have := congrArg List.length he
        simp [List.length_take, Nat.min_eq_left hkw] at this
        omega
      · exact hGn u hu
    · rintro ⟨hl, hw, hn⟩
      cases F with
      | nil => simp at hl
      | cons u G =>
        have hun := hn u (by simp)
        have hul : 1 ≤ u.length := by
          have := List.length_pos_iff.mpr hun
          omega
        have hlen : u.length ≤ w.length := by
          rw [← hw]; simp
        refine ⟨u.length, ⟨hul, hlen⟩, G, ?_, ?_⟩
        · apply ih.mpr
          refine ⟨by simpa using hl, ?_, fun v hv => hn v (by simp [hv])⟩
          rw [← hw]
          simp
        · rw [← hw]
          simp

 theorem sections_one (w : List ℕ) (hw : w ≠ []) : sections 1 w = {[w]} := by
  ext F
  rw [mem_sections]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨hl, he, _⟩
    cases F with
    | nil => simp at hl
    | cons u G =>
      have hG : G = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst G
      simpa using congrArg (fun x => [x]) he
  · rintro rfl
    simp [hw]

 theorem tuples_one (M : ℕ) (hM : 0 < M) :
    tuples M 1 = (words M).image (fun w => [w]) := by
  ext F
  simp only [tuples, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hF⟩
    have hn : w ≠ [] := by
      intro he
      have hl := (mem_words.mp hw).length_eq
      simp [he] at hl
      omega
    rw [sections_one w hn, Finset.mem_singleton] at hF
    exact ⟨w, hw, hF.symm⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, hw, mem_sections.mpr ?_⟩
    refine ⟨by simp, by simp, ?_⟩
    intro u hu
    have : u = w := by simpa using hu
    subst u
    intro he
    have hl := (mem_words.mp hw).length_eq
    simp [he] at hl
    omega

 theorem XI_one (M : ℕ) (hM : 0 < M) : XI M 1 1 = P M := by
  classical
  unfold XI P
  rw [tuples_one M hM]
  apply Finset.card_bij (fun p _ => (p.1.headD [], p.2.headD []))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image] at hp ⊢
    rcases hp with ⟨⟨⟨u, hu, heu⟩, ⟨v, hv, hev⟩⟩, he⟩
    rw [← heu, ← hev] at he ⊢
    simpa [output] using And.intro (And.intro hu hv) he
  · intro p hp q hq he
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image] at hp hq
    rcases hp.1 with ⟨⟨u, _, hu⟩, ⟨v, _, hv⟩⟩
    rcases hq.1 with ⟨⟨u', _, hu'⟩, ⟨v', _, hv'⟩⟩
    apply Prod.ext
    · simpa [← hu, ← hu'] using congrArg (fun x => [x.1]) he
    · simpa [← hv, ← hv'] using congrArg (fun x => [x.2]) he
  · intro p hp
    refine ⟨([p.1], [p.2]), ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image] at hp ⊢
    exact ⟨⟨⟨p.1, hp.1.1, rfl⟩, ⟨p.2, hp.1.2, rfl⟩⟩, by simpa [output] using hp.2⟩

end StackSort.Seeds2
