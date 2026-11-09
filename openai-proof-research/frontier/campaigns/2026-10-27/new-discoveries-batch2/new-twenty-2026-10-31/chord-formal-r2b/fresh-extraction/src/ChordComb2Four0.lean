import ChordComb2OrbitFour
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d4_0_0 : Diagram 4 := tableDiagram (by decide) [1, 0, 3, 2, 5, 4, 7, 6] (by decide) (by decide)
theorem cert4_0_0 : Range12 d4_0_0 → ∃ i, Equivalent d4_0_0 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_0 0 := ⟨maskSides 4 0, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_1 : Diagram 4 := tableDiagram (by decide) [1, 0, 3, 2, 6, 7, 4, 5] (by decide) (by decide)
theorem cert4_0_1 : Range12 d4_0_1 → ∃ i, Equivalent d4_0_1 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_1 0 := ⟨maskSides 4 80, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_2 : Diagram 4 := tableDiagram (by decide) [1, 0, 3, 2, 7, 6, 5, 4] (by decide) (by decide)
theorem cert4_0_2 : Range12 d4_0_2 → ∃ i, Equivalent d4_0_2 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_2 0 := ⟨maskSides 4 0, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_3 : Diagram 4 := tableDiagram (by decide) [1, 0, 4, 5, 2, 3, 7, 6] (by decide) (by decide)
theorem cert4_0_3 : Range12 d4_0_3 → ∃ i, Equivalent d4_0_3 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_3 0 := ⟨maskSides 4 20, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_4 : Diagram 4 := tableDiagram (by decide) [1, 0, 4, 6, 2, 7, 3, 5] (by decide) (by decide)
theorem cert4_0_4 : Range12 d4_0_4 → ∃ i, Equivalent d4_0_4 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_4 0 := ⟨maskSides 4 72, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_5 : Diagram 4 := tableDiagram (by decide) [1, 0, 4, 7, 2, 6, 5, 3] (by decide) (by decide)
theorem cert4_0_5 : Range12 d4_0_5 → ∃ i, Equivalent d4_0_5 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_5 0 := ⟨maskSides 4 20, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_6 : Diagram 4 := tableDiagram (by decide) [1, 0, 5, 4, 3, 2, 7, 6] (by decide) (by decide)
theorem cert4_0_6 : Range12 d4_0_6 → ∃ i, Equivalent d4_0_6 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_6 0 := ⟨maskSides 4 0, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_7 : Diagram 4 := tableDiagram (by decide) [1, 0, 5, 6, 7, 2, 3, 4] (by decide) (by decide)
theorem cert4_0_7 : Range12 d4_0_7 → ∃ i, Equivalent d4_0_7 (fourReps i) := by
  intro _
  refine ⟨0, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨0, false, by decide⟩
def d4_0_8 : Diagram 4 := tableDiagram (by decide) [1, 0, 5, 7, 6, 2, 4, 3] (by decide) (by decide)
theorem cert4_0_8 : Range12 d4_0_8 → ∃ i, Equivalent d4_0_8 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_8 0 := ⟨maskSides 4 36, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_9 : Diagram 4 := tableDiagram (by decide) [1, 0, 6, 4, 3, 7, 2, 5] (by decide) (by decide)
theorem cert4_0_9 : Range12 d4_0_9 → ∃ i, Equivalent d4_0_9 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_9 0 := ⟨maskSides 4 68, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_10 : Diagram 4 := tableDiagram (by decide) [1, 0, 6, 5, 7, 3, 2, 4] (by decide) (by decide)
theorem cert4_0_10 : Range12 d4_0_10 → ∃ i, Equivalent d4_0_10 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_10 0 := ⟨maskSides 4 108, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_11 : Diagram 4 := tableDiagram (by decide) [1, 0, 6, 7, 5, 4, 2, 3] (by decide) (by decide)
theorem cert4_0_11 : Range12 d4_0_11 → ∃ i, Equivalent d4_0_11 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_11 0 := ⟨maskSides 4 68, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_12 : Diagram 4 := tableDiagram (by decide) [1, 0, 7, 4, 3, 6, 5, 2] (by decide) (by decide)
theorem cert4_0_12 : Range12 d4_0_12 → ∃ i, Equivalent d4_0_12 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_12 0 := ⟨maskSides 4 0, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_13 : Diagram 4 := tableDiagram (by decide) [1, 0, 7, 5, 6, 3, 4, 2] (by decide) (by decide)
theorem cert4_0_13 : Range12 d4_0_13 → ∃ i, Equivalent d4_0_13 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_13 0 := ⟨maskSides 4 40, by decide⟩
  have := (h 0).mp hg
  omega
def d4_0_14 : Diagram 4 := tableDiagram (by decide) [1, 0, 7, 6, 5, 4, 3, 2] (by decide) (by decide)
theorem cert4_0_14 : Range12 d4_0_14 → ∃ i, Equivalent d4_0_14 (fourReps i) := by
  intro h
  have hg : genusRange d4_0_14 0 := ⟨maskSides 4 0, by decide⟩
  have := (h 0).mp hg
  omega
theorem cases4_0 (P : Diagram 4 → Prop)
    (c0 : P d4_0_0)
    (c1 : P d4_0_1)
    (c2 : P d4_0_2)
    (c3 : P d4_0_3)
    (c4 : P d4_0_4)
    (c5 : P d4_0_5)
    (c6 : P d4_0_6)
    (c7 : P d4_0_7)
    (c8 : P d4_0_8)
    (c9 : P d4_0_9)
    (c10 : P d4_0_10)
    (c11 : P d4_0_11)
    (c12 : P d4_0_12)
    (c13 : P d4_0_13)
    (c14 : P d4_0_14)
    (D : Diagram 4) (h0 : D.partner 0 = 1) (h1 : D.partner 1 = 0) : P D := by
  have opts : D.partner 2 = 3 ∨ D.partner 2 = 4 ∨ D.partner 2 = 5 ∨ D.partner 2 = 6 ∨ D.partner 2 = 7 := by
    have inv := D.involutive 2
    have nf := D.noFixed 2
    generalize hv : D.partner 2 = v
    fin_cases v <;> simp_all
  rcases opts with h2_3 | h2_4 | h2_5 | h2_6 | h2_7
  · have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
    have opts : D.partner 4 = 5 ∨ D.partner 4 = 6 ∨ D.partner 4 = 7 := by
      have inv := D.involutive 4
      have nf := D.noFixed 4
      generalize hv : D.partner 4 = v
      fin_cases v <;> simp_all
    rcases opts with h4_5 | h4_6 | h4_7
    · have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d4_0_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_0_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_0_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
    have opts : D.partner 3 = 5 ∨ D.partner 3 = 6 ∨ D.partner 3 = 7 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_5 | h3_6 | h3_7
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d4_0_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_0_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_0_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
    have opts : D.partner 3 = 4 ∨ D.partner 3 = 6 ∨ D.partner 3 = 7 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_4 | h3_6 | h3_7
    · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d4_0_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d4_0_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 4 = 6 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_6 := opts
      have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have hd : D = d4_0_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
    have opts : D.partner 3 = 4 ∨ D.partner 3 = 5 ∨ D.partner 3 = 7 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_4 | h3_5 | h3_7
    · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_0_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d4_0_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d4_0_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
    have opts : D.partner 3 = 4 ∨ D.partner 3 = 5 ∨ D.partner 3 = 6 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_4 | h3_5 | h3_6
    · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_0_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 4 = 6 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_6 := opts
      have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have hd : D = d4_0_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d4_0_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_0_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed4_0 (D : Diagram 4) (h0 : D.partner 0 = 1) (h1 : D.partner 1 = 0) : Range12 D → ∃ i, Equivalent D (fourReps i) :=
  cases4_0 (fun E => Range12 E → ∃ i, Equivalent E (fourReps i)) cert4_0_0 cert4_0_1 cert4_0_2 cert4_0_3 cert4_0_4 cert4_0_5 cert4_0_6 cert4_0_7 cert4_0_8 cert4_0_9 cert4_0_10 cert4_0_11 cert4_0_12 cert4_0_13 cert4_0_14 D h0 h1
end Chord.Comb2
