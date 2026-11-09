import ChordComb2OrbitFour
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d4_3_0 : Diagram 4 := tableDiagram (by decide) [4, 2, 1, 5, 0, 3, 7, 6] (by decide) (by decide)
theorem cert4_3_0 : Range12 d4_3_0 → ∃ i, Equivalent d4_3_0 (fourReps i) := by
  intro h
  have hg : genusRange d4_3_0 0 := ⟨maskSides 4 17, by decide⟩
  have := (h 0).mp hg
  omega
def d4_3_1 : Diagram 4 := tableDiagram (by decide) [4, 2, 1, 6, 0, 7, 3, 5] (by decide) (by decide)
theorem cert4_3_1 : Range12 d4_3_1 → ∃ i, Equivalent d4_3_1 (fourReps i) := by
  intro h
  have hg : genusRange d4_3_1 0 := ⟨maskSides 4 72, by decide⟩
  have := (h 0).mp hg
  omega
def d4_3_2 : Diagram 4 := tableDiagram (by decide) [4, 2, 1, 7, 0, 6, 5, 3] (by decide) (by decide)
theorem cert4_3_2 : Range12 d4_3_2 → ∃ i, Equivalent d4_3_2 (fourReps i) := by
  intro h
  have hg : genusRange d4_3_2 0 := ⟨maskSides 4 17, by decide⟩
  have := (h 0).mp hg
  omega
def d4_3_3 : Diagram 4 := tableDiagram (by decide) [4, 3, 5, 1, 0, 2, 7, 6] (by decide) (by decide)
theorem cert4_3_3 : Range12 d4_3_3 → ∃ i, Equivalent d4_3_3 (fourReps i) := by
  intro h
  have hg : genusRange d4_3_3 0 := ⟨maskSides 4 27, by decide⟩
  have := (h 0).mp hg
  omega
def d4_3_4 : Diagram 4 := tableDiagram (by decide) [4, 3, 6, 1, 0, 7, 2, 5] (by decide) (by decide)
theorem cert4_3_4 : Range12 d4_3_4 → ∃ i, Equivalent d4_3_4 (fourReps i) := by
  intro h
  have hg : genusRange d4_3_4 0 := ⟨maskSides 4 68, by decide⟩
  have := (h 0).mp hg
  omega
def d4_3_5 : Diagram 4 := tableDiagram (by decide) [4, 3, 7, 1, 0, 6, 5, 2] (by decide) (by decide)
theorem cert4_3_5 : Range12 d4_3_5 → ∃ i, Equivalent d4_3_5 (fourReps i) := by
  intro h
  have hg : genusRange d4_3_5 0 := ⟨maskSides 4 27, by decide⟩
  have := (h 0).mp hg
  omega
def d4_3_6 : Diagram 4 := tableDiagram (by decide) [4, 5, 3, 2, 0, 1, 7, 6] (by decide) (by decide)
theorem cert4_3_6 : Range12 d4_3_6 → ∃ i, Equivalent d4_3_6 (fourReps i) := by
  intro h
  have hg : genusRange d4_3_6 0 := ⟨maskSides 4 17, by decide⟩
  have := (h 0).mp hg
  omega
def d4_3_7 : Diagram 4 := tableDiagram (by decide) [4, 5, 6, 7, 0, 1, 2, 3] (by decide) (by decide)
theorem cert4_3_7 : Range12 d4_3_7 → ∃ i, Equivalent d4_3_7 (fourReps i) := by
  intro _
  refine ⟨3, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨0, false, by decide⟩
def d4_3_8 : Diagram 4 := tableDiagram (by decide) [4, 5, 7, 6, 0, 1, 3, 2] (by decide) (by decide)
theorem cert4_3_8 : Range12 d4_3_8 → ∃ i, Equivalent d4_3_8 (fourReps i) := by
  intro _
  refine ⟨2, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨1, false, by decide⟩
def d4_3_9 : Diagram 4 := tableDiagram (by decide) [4, 6, 3, 2, 0, 7, 1, 5] (by decide) (by decide)
theorem cert4_3_9 : Range12 d4_3_9 → ∃ i, Equivalent d4_3_9 (fourReps i) := by
  intro h
  have hg : genusRange d4_3_9 0 := ⟨maskSides 4 66, by decide⟩
  have := (h 0).mp hg
  omega
def d4_3_10 : Diagram 4 := tableDiagram (by decide) [4, 6, 5, 7, 0, 2, 1, 3] (by decide) (by decide)
theorem cert4_3_10 : Range12 d4_3_10 → ∃ i, Equivalent d4_3_10 (fourReps i) := by
  intro _
  refine ⟨2, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨2, false, by decide⟩
def d4_3_11 : Diagram 4 := tableDiagram (by decide) [4, 6, 7, 5, 0, 3, 1, 2] (by decide) (by decide)
theorem cert4_3_11 : Range12 d4_3_11 → ∃ i, Equivalent d4_3_11 (fourReps i) := by
  intro _
  refine ⟨1, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨5, false, by decide⟩
def d4_3_12 : Diagram 4 := tableDiagram (by decide) [4, 7, 3, 2, 0, 6, 5, 1] (by decide) (by decide)
theorem cert4_3_12 : Range12 d4_3_12 → ∃ i, Equivalent d4_3_12 (fourReps i) := by
  intro h
  have hg : genusRange d4_3_12 0 := ⟨maskSides 4 17, by decide⟩
  have := (h 0).mp hg
  omega
def d4_3_13 : Diagram 4 := tableDiagram (by decide) [4, 7, 5, 6, 0, 2, 3, 1] (by decide) (by decide)
theorem cert4_3_13 : Range12 d4_3_13 → ∃ i, Equivalent d4_3_13 (fourReps i) := by
  intro _
  refine ⟨1, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨1, false, by decide⟩
def d4_3_14 : Diagram 4 := tableDiagram (by decide) [4, 7, 6, 5, 0, 3, 2, 1] (by decide) (by decide)
theorem cert4_3_14 : Range12 d4_3_14 → ∃ i, Equivalent d4_3_14 (fourReps i) := by
  intro h
  have hg : genusRange d4_3_14 0 := ⟨maskSides 4 17, by decide⟩
  have := (h 0).mp hg
  omega
theorem cases4_3 (P : Diagram 4 → Prop)
    (c0 : P d4_3_0)
    (c1 : P d4_3_1)
    (c2 : P d4_3_2)
    (c3 : P d4_3_3)
    (c4 : P d4_3_4)
    (c5 : P d4_3_5)
    (c6 : P d4_3_6)
    (c7 : P d4_3_7)
    (c8 : P d4_3_8)
    (c9 : P d4_3_9)
    (c10 : P d4_3_10)
    (c11 : P d4_3_11)
    (c12 : P d4_3_12)
    (c13 : P d4_3_13)
    (c14 : P d4_3_14)
    (D : Diagram 4) (h0 : D.partner 0 = 4) (h4 : D.partner 4 = 0) : P D := by
  have opts : D.partner 1 = 2 ∨ D.partner 1 = 3 ∨ D.partner 1 = 5 ∨ D.partner 1 = 6 ∨ D.partner 1 = 7 := by
    have inv := D.involutive 1
    have nf := D.noFixed 1
    generalize hv : D.partner 1 = v
    fin_cases v <;> simp_all
  rcases opts with h1_2 | h1_3 | h1_5 | h1_6 | h1_7
  · have h2 : D.partner 2 = 1 := by simpa only [h1_2] using D.involutive 1
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
      have hd : D = d4_3_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_3_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_3_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h3 : D.partner 3 = 1 := by simpa only [h1_3] using D.involutive 1
    have opts : D.partner 2 = 5 ∨ D.partner 2 = 6 ∨ D.partner 2 = 7 := by
      have inv := D.involutive 2
      have nf := D.noFixed 2
      generalize hv : D.partner 2 = v
      fin_cases v <;> simp_all
    rcases opts with h2_5 | h2_6 | h2_7
    · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d4_3_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_3_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_3_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h5 : D.partner 5 = 1 := by simpa only [h1_5] using D.involutive 1
    have opts : D.partner 2 = 3 ∨ D.partner 2 = 6 ∨ D.partner 2 = 7 := by
      have inv := D.involutive 2
      have nf := D.noFixed 2
      generalize hv : D.partner 2 = v
      fin_cases v <;> simp_all
    rcases opts with h2_3 | h2_6 | h2_7
    · have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d4_3_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
      have opts : D.partner 3 = 7 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_7 := opts
      have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have hd : D = d4_3_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
      have opts : D.partner 3 = 6 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_6 := opts
      have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have hd : D = d4_3_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h6 : D.partner 6 = 1 := by simpa only [h1_6] using D.involutive 1
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
      have hd : D = d4_3_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have opts : D.partner 3 = 7 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_7 := opts
      have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have hd : D = d4_3_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
      have opts : D.partner 3 = 5 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_5 := opts
      have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have hd : D = d4_3_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h7 : D.partner 7 = 1 := by simpa only [h1_7] using D.involutive 1
    have opts : D.partner 2 = 3 ∨ D.partner 2 = 5 ∨ D.partner 2 = 6 := by
      have inv := D.involutive 2
      have nf := D.noFixed 2
      generalize hv : D.partner 2 = v
      fin_cases v <;> simp_all
    rcases opts with h2_3 | h2_5 | h2_6
    · have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_3_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have opts : D.partner 3 = 6 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_6 := opts
      have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have hd : D = d4_3_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
      have opts : D.partner 3 = 5 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_5 := opts
      have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have hd : D = d4_3_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_3_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed4_3 (D : Diagram 4) (h0 : D.partner 0 = 4) (h4 : D.partner 4 = 0) : Range12 D → ∃ i, Equivalent D (fourReps i) :=
  cases4_3 (fun E => Range12 E → ∃ i, Equivalent E (fourReps i)) cert4_3_0 cert4_3_1 cert4_3_2 cert4_3_3 cert4_3_4 cert4_3_5 cert4_3_6 cert4_3_7 cert4_3_8 cert4_3_9 cert4_3_10 cert4_3_11 cert4_3_12 cert4_3_13 cert4_3_14 D h0 h4
end Chord.Comb2
