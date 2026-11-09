import ChordComb2OrbitFour
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d4_1_0 : Diagram 4 := tableDiagram (by decide) [2, 3, 0, 1, 5, 4, 7, 6] (by decide) (by decide)
theorem cert4_1_0 : Range12 d4_1_0 → ∃ i, Equivalent d4_1_0 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_0 0 := ⟨maskSides 4 5, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_1 : Diagram 4 := tableDiagram (by decide) [2, 3, 0, 1, 6, 7, 4, 5] (by decide) (by decide)
theorem cert4_1_1 : Range12 d4_1_1 → ∃ i, Equivalent d4_1_1 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_1 0 := ⟨maskSides 4 85, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_2 : Diagram 4 := tableDiagram (by decide) [2, 3, 0, 1, 7, 6, 5, 4] (by decide) (by decide)
theorem cert4_1_2 : Range12 d4_1_2 → ∃ i, Equivalent d4_1_2 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_2 0 := ⟨maskSides 4 5, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_3 : Diagram 4 := tableDiagram (by decide) [2, 4, 0, 5, 1, 3, 7, 6] (by decide) (by decide)
theorem cert4_1_3 : Range12 d4_1_3 → ∃ i, Equivalent d4_1_3 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_3 0 := ⟨maskSides 4 18, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_4 : Diagram 4 := tableDiagram (by decide) [2, 4, 0, 6, 1, 7, 3, 5] (by decide) (by decide)
theorem cert4_1_4 : Range12 d4_1_4 → ∃ i, Equivalent d4_1_4 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_4 0 := ⟨maskSides 4 77, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_5 : Diagram 4 := tableDiagram (by decide) [2, 4, 0, 7, 1, 6, 5, 3] (by decide) (by decide)
theorem cert4_1_5 : Range12 d4_1_5 → ∃ i, Equivalent d4_1_5 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_5 0 := ⟨maskSides 4 18, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_6 : Diagram 4 := tableDiagram (by decide) [2, 5, 0, 4, 3, 1, 7, 6] (by decide) (by decide)
theorem cert4_1_6 : Range12 d4_1_6 → ∃ i, Equivalent d4_1_6 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_6 0 := ⟨maskSides 4 5, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_7 : Diagram 4 := tableDiagram (by decide) [2, 5, 0, 6, 7, 1, 3, 4] (by decide) (by decide)
theorem cert4_1_7 : Range12 d4_1_7 → ∃ i, Equivalent d4_1_7 (fourReps i) := by
  intro _
  refine ⟨1, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨0, false, by decide⟩
def d4_1_8 : Diagram 4 := tableDiagram (by decide) [2, 5, 0, 7, 6, 1, 4, 3] (by decide) (by decide)
theorem cert4_1_8 : Range12 d4_1_8 → ∃ i, Equivalent d4_1_8 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_8 0 := ⟨maskSides 4 34, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_9 : Diagram 4 := tableDiagram (by decide) [2, 6, 0, 4, 3, 7, 1, 5] (by decide) (by decide)
theorem cert4_1_9 : Range12 d4_1_9 → ∃ i, Equivalent d4_1_9 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_9 0 := ⟨maskSides 4 66, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_10 : Diagram 4 := tableDiagram (by decide) [2, 6, 0, 5, 7, 3, 1, 4] (by decide) (by decide)
theorem cert4_1_10 : Range12 d4_1_10 → ∃ i, Equivalent d4_1_10 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_10 0 := ⟨maskSides 4 106, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_11 : Diagram 4 := tableDiagram (by decide) [2, 6, 0, 7, 5, 4, 1, 3] (by decide) (by decide)
theorem cert4_1_11 : Range12 d4_1_11 → ∃ i, Equivalent d4_1_11 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_11 0 := ⟨maskSides 4 66, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_12 : Diagram 4 := tableDiagram (by decide) [2, 7, 0, 4, 3, 6, 5, 1] (by decide) (by decide)
theorem cert4_1_12 : Range12 d4_1_12 → ∃ i, Equivalent d4_1_12 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_12 0 := ⟨maskSides 4 5, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_13 : Diagram 4 := tableDiagram (by decide) [2, 7, 0, 5, 6, 3, 4, 1] (by decide) (by decide)
theorem cert4_1_13 : Range12 d4_1_13 → ∃ i, Equivalent d4_1_13 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_13 0 := ⟨maskSides 4 45, by decide⟩
  have := (h 0).mp hg
  omega
def d4_1_14 : Diagram 4 := tableDiagram (by decide) [2, 7, 0, 6, 5, 4, 3, 1] (by decide) (by decide)
theorem cert4_1_14 : Range12 d4_1_14 → ∃ i, Equivalent d4_1_14 (fourReps i) := by
  intro h
  have hg : genusRange d4_1_14 0 := ⟨maskSides 4 5, by decide⟩
  have := (h 0).mp hg
  omega
theorem cases4_1 (P : Diagram 4 → Prop)
    (c0 : P d4_1_0)
    (c1 : P d4_1_1)
    (c2 : P d4_1_2)
    (c3 : P d4_1_3)
    (c4 : P d4_1_4)
    (c5 : P d4_1_5)
    (c6 : P d4_1_6)
    (c7 : P d4_1_7)
    (c8 : P d4_1_8)
    (c9 : P d4_1_9)
    (c10 : P d4_1_10)
    (c11 : P d4_1_11)
    (c12 : P d4_1_12)
    (c13 : P d4_1_13)
    (c14 : P d4_1_14)
    (D : Diagram 4) (h0 : D.partner 0 = 2) (h2 : D.partner 2 = 0) : P D := by
  have opts : D.partner 1 = 3 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 ∨ D.partner 1 = 6 ∨ D.partner 1 = 7 := by
    have inv := D.involutive 1
    have nf := D.noFixed 1
    generalize hv : D.partner 1 = v
    fin_cases v <;> simp_all
  rcases opts with h1_3 | h1_4 | h1_5 | h1_6 | h1_7
  · have h3 : D.partner 3 = 1 := by simpa only [h1_3] using D.involutive 1
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
      have hd : D = d4_1_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_1_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_1_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h4 : D.partner 4 = 1 := by simpa only [h1_4] using D.involutive 1
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
      have hd : D = d4_1_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_1_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_1_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h5 : D.partner 5 = 1 := by simpa only [h1_5] using D.involutive 1
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
      have hd : D = d4_1_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d4_1_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 4 = 6 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_6 := opts
      have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have hd : D = d4_1_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h6 : D.partner 6 = 1 := by simpa only [h1_6] using D.involutive 1
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
      have hd : D = d4_1_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d4_1_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d4_1_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h7 : D.partner 7 = 1 := by simpa only [h1_7] using D.involutive 1
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
      have hd : D = d4_1_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 4 = 6 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_6 := opts
      have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have hd : D = d4_1_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d4_1_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_1_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed4_1 (D : Diagram 4) (h0 : D.partner 0 = 2) (h2 : D.partner 2 = 0) : Range12 D → ∃ i, Equivalent D (fourReps i) :=
  cases4_1 (fun E => Range12 E → ∃ i, Equivalent E (fourReps i)) cert4_1_0 cert4_1_1 cert4_1_2 cert4_1_3 cert4_1_4 cert4_1_5 cert4_1_6 cert4_1_7 cert4_1_8 cert4_1_9 cert4_1_10 cert4_1_11 cert4_1_12 cert4_1_13 cert4_1_14 D h0 h2
end Chord.Comb2
