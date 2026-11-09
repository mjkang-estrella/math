import ChordComb2OrbitFour
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d4_5_0 : Diagram 4 := tableDiagram (by decide) [6, 2, 1, 4, 3, 7, 0, 5] (by decide) (by decide)
theorem cert4_5_0 : Range12 d4_5_0 → ∃ i, Equivalent d4_5_0 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_0 0 := ⟨maskSides 4 65, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_1 : Diagram 4 := tableDiagram (by decide) [6, 2, 1, 5, 7, 3, 0, 4] (by decide) (by decide)
theorem cert4_5_1 : Range12 d4_5_1 → ∃ i, Equivalent d4_5_1 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_1 0 := ⟨maskSides 4 105, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_2 : Diagram 4 := tableDiagram (by decide) [6, 2, 1, 7, 5, 4, 0, 3] (by decide) (by decide)
theorem cert4_5_2 : Range12 d4_5_2 → ∃ i, Equivalent d4_5_2 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_2 0 := ⟨maskSides 4 65, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_3 : Diagram 4 := tableDiagram (by decide) [6, 3, 4, 1, 2, 7, 0, 5] (by decide) (by decide)
theorem cert4_5_3 : Range12 d4_5_3 → ∃ i, Equivalent d4_5_3 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_3 0 := ⟨maskSides 4 75, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_4 : Diagram 4 := tableDiagram (by decide) [6, 3, 5, 1, 7, 2, 0, 4] (by decide) (by decide)
theorem cert4_5_4 : Range12 d4_5_4 → ∃ i, Equivalent d4_5_4 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_4 0 := ⟨maskSides 4 101, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_5 : Diagram 4 := tableDiagram (by decide) [6, 3, 7, 1, 5, 4, 0, 2] (by decide) (by decide)
theorem cert4_5_5 : Range12 d4_5_5 → ∃ i, Equivalent d4_5_5 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_5 0 := ⟨maskSides 4 75, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_6 : Diagram 4 := tableDiagram (by decide) [6, 4, 3, 2, 1, 7, 0, 5] (by decide) (by decide)
theorem cert4_5_6 : Range12 d4_5_6 → ∃ i, Equivalent d4_5_6 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_6 0 := ⟨maskSides 4 65, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_7 : Diagram 4 := tableDiagram (by decide) [6, 4, 5, 7, 1, 2, 0, 3] (by decide) (by decide)
theorem cert4_5_7 : Range12 d4_5_7 → ∃ i, Equivalent d4_5_7 (fourReps i) := by
  intro _
  refine ⟨1, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨2, false, by decide⟩
def d4_5_8 : Diagram 4 := tableDiagram (by decide) [6, 4, 7, 5, 1, 3, 0, 2] (by decide) (by decide)
theorem cert4_5_8 : Range12 d4_5_8 → ∃ i, Equivalent d4_5_8 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_8 0 := ⟨maskSides 4 83, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_9 : Diagram 4 := tableDiagram (by decide) [6, 5, 3, 2, 7, 1, 0, 4] (by decide) (by decide)
theorem cert4_5_9 : Range12 d4_5_9 → ∃ i, Equivalent d4_5_9 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_9 0 := ⟨maskSides 4 99, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_10 : Diagram 4 := tableDiagram (by decide) [6, 5, 4, 7, 2, 1, 0, 3] (by decide) (by decide)
theorem cert4_5_10 : Range12 d4_5_10 → ∃ i, Equivalent d4_5_10 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_10 0 := ⟨maskSides 4 119, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_11 : Diagram 4 := tableDiagram (by decide) [6, 5, 7, 4, 3, 1, 0, 2] (by decide) (by decide)
theorem cert4_5_11 : Range12 d4_5_11 → ∃ i, Equivalent d4_5_11 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_11 0 := ⟨maskSides 4 99, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_12 : Diagram 4 := tableDiagram (by decide) [6, 7, 3, 2, 5, 4, 0, 1] (by decide) (by decide)
theorem cert4_5_12 : Range12 d4_5_12 → ∃ i, Equivalent d4_5_12 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_12 0 := ⟨maskSides 4 65, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_13 : Diagram 4 := tableDiagram (by decide) [6, 7, 4, 5, 2, 3, 0, 1] (by decide) (by decide)
theorem cert4_5_13 : Range12 d4_5_13 → ∃ i, Equivalent d4_5_13 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_13 0 := ⟨maskSides 4 85, by decide⟩
  have := (h 0).mp hg
  omega
def d4_5_14 : Diagram 4 := tableDiagram (by decide) [6, 7, 5, 4, 3, 2, 0, 1] (by decide) (by decide)
theorem cert4_5_14 : Range12 d4_5_14 → ∃ i, Equivalent d4_5_14 (fourReps i) := by
  intro h
  have hg : genusRange d4_5_14 0 := ⟨maskSides 4 65, by decide⟩
  have := (h 0).mp hg
  omega
theorem cases4_5 (P : Diagram 4 → Prop)
    (c0 : P d4_5_0)
    (c1 : P d4_5_1)
    (c2 : P d4_5_2)
    (c3 : P d4_5_3)
    (c4 : P d4_5_4)
    (c5 : P d4_5_5)
    (c6 : P d4_5_6)
    (c7 : P d4_5_7)
    (c8 : P d4_5_8)
    (c9 : P d4_5_9)
    (c10 : P d4_5_10)
    (c11 : P d4_5_11)
    (c12 : P d4_5_12)
    (c13 : P d4_5_13)
    (c14 : P d4_5_14)
    (D : Diagram 4) (h0 : D.partner 0 = 6) (h6 : D.partner 6 = 0) : P D := by
  have opts : D.partner 1 = 2 ∨ D.partner 1 = 3 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 ∨ D.partner 1 = 7 := by
    have inv := D.involutive 1
    have nf := D.noFixed 1
    generalize hv : D.partner 1 = v
    fin_cases v <;> simp_all
  rcases opts with h1_2 | h1_3 | h1_4 | h1_5 | h1_7
  · have h2 : D.partner 2 = 1 := by simpa only [h1_2] using D.involutive 1
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
      have hd : D = d4_5_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d4_5_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d4_5_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h3 : D.partner 3 = 1 := by simpa only [h1_3] using D.involutive 1
    have opts : D.partner 2 = 4 ∨ D.partner 2 = 5 ∨ D.partner 2 = 7 := by
      have inv := D.involutive 2
      have nf := D.noFixed 2
      generalize hv : D.partner 2 = v
      fin_cases v <;> simp_all
    rcases opts with h2_4 | h2_5 | h2_7
    · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_5_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d4_5_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d4_5_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h4 : D.partner 4 = 1 := by simpa only [h1_4] using D.involutive 1
    have opts : D.partner 2 = 3 ∨ D.partner 2 = 5 ∨ D.partner 2 = 7 := by
      have inv := D.involutive 2
      have nf := D.noFixed 2
      generalize hv : D.partner 2 = v
      fin_cases v <;> simp_all
    rcases opts with h2_3 | h2_5 | h2_7
    · have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_5_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have opts : D.partner 3 = 7 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_7 := opts
      have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have hd : D = d4_5_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
      have opts : D.partner 3 = 5 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_5 := opts
      have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have hd : D = d4_5_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h5 : D.partner 5 = 1 := by simpa only [h1_5] using D.involutive 1
    have opts : D.partner 2 = 3 ∨ D.partner 2 = 4 ∨ D.partner 2 = 7 := by
      have inv := D.involutive 2
      have nf := D.noFixed 2
      generalize hv : D.partner 2 = v
      fin_cases v <;> simp_all
    rcases opts with h2_3 | h2_4 | h2_7
    · have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d4_5_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
      have opts : D.partner 3 = 7 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_7 := opts
      have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have hd : D = d4_5_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
      have opts : D.partner 3 = 4 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_4 := opts
      have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have hd : D = d4_5_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h7 : D.partner 7 = 1 := by simpa only [h1_7] using D.involutive 1
    have opts : D.partner 2 = 3 ∨ D.partner 2 = 4 ∨ D.partner 2 = 5 := by
      have inv := D.involutive 2
      have nf := D.noFixed 2
      generalize hv : D.partner 2 = v
      fin_cases v <;> simp_all
    rcases opts with h2_3 | h2_4 | h2_5
    · have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d4_5_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
      have opts : D.partner 3 = 5 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_5 := opts
      have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have hd : D = d4_5_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have opts : D.partner 3 = 4 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_4 := opts
      have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have hd : D = d4_5_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_5_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed4_5 (D : Diagram 4) (h0 : D.partner 0 = 6) (h6 : D.partner 6 = 0) : Range12 D → ∃ i, Equivalent D (fourReps i) :=
  cases4_5 (fun E => Range12 E → ∃ i, Equivalent E (fourReps i)) cert4_5_0 cert4_5_1 cert4_5_2 cert4_5_3 cert4_5_4 cert4_5_5 cert4_5_6 cert4_5_7 cert4_5_8 cert4_5_9 cert4_5_10 cert4_5_11 cert4_5_12 cert4_5_13 cert4_5_14 D h0 h6
end Chord.Comb2
