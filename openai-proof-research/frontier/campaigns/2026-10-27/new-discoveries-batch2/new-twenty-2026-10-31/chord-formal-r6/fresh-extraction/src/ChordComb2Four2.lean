import ChordComb2OrbitFour
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d4_2_0 : Diagram 4 := tableDiagram (by decide) [3, 2, 1, 0, 5, 4, 7, 6] (by decide) (by decide)
theorem cert4_2_0 : Range12 d4_2_0 → ∃ i, Equivalent d4_2_0 (fourReps i) := by
  intro h
  have hg : genusRange d4_2_0 0 := ⟨maskSides 4 0, by decide⟩
  have := (h 0).mp hg
  omega
def d4_2_1 : Diagram 4 := tableDiagram (by decide) [3, 2, 1, 0, 6, 7, 4, 5] (by decide) (by decide)
theorem cert4_2_1 : Range12 d4_2_1 → ∃ i, Equivalent d4_2_1 (fourReps i) := by
  intro h
  have hg : genusRange d4_2_1 0 := ⟨maskSides 4 80, by decide⟩
  have := (h 0).mp hg
  omega
def d4_2_2 : Diagram 4 := tableDiagram (by decide) [3, 2, 1, 0, 7, 6, 5, 4] (by decide) (by decide)
theorem cert4_2_2 : Range12 d4_2_2 → ∃ i, Equivalent d4_2_2 (fourReps i) := by
  intro h
  have hg : genusRange d4_2_2 0 := ⟨maskSides 4 0, by decide⟩
  have := (h 0).mp hg
  omega
def d4_2_3 : Diagram 4 := tableDiagram (by decide) [3, 4, 5, 0, 1, 2, 7, 6] (by decide) (by decide)
theorem cert4_2_3 : Range12 d4_2_3 → ∃ i, Equivalent d4_2_3 (fourReps i) := by
  intro _
  refine ⟨0, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨2, false, by decide⟩
def d4_2_4 : Diagram 4 := tableDiagram (by decide) [3, 4, 6, 0, 1, 7, 2, 5] (by decide) (by decide)
theorem cert4_2_4 : Range12 d4_2_4 → ∃ i, Equivalent d4_2_4 (fourReps i) := by
  intro _
  refine ⟨1, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨3, false, by decide⟩
def d4_2_5 : Diagram 4 := tableDiagram (by decide) [3, 4, 7, 0, 1, 6, 5, 2] (by decide) (by decide)
theorem cert4_2_5 : Range12 d4_2_5 → ∃ i, Equivalent d4_2_5 (fourReps i) := by
  intro _
  refine ⟨0, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨3, false, by decide⟩
def d4_2_6 : Diagram 4 := tableDiagram (by decide) [3, 5, 4, 0, 2, 1, 7, 6] (by decide) (by decide)
theorem cert4_2_6 : Range12 d4_2_6 → ∃ i, Equivalent d4_2_6 (fourReps i) := by
  intro h
  have hg : genusRange d4_2_6 0 := ⟨maskSides 4 9, by decide⟩
  have := (h 0).mp hg
  omega
def d4_2_7 : Diagram 4 := tableDiagram (by decide) [3, 5, 6, 0, 7, 1, 2, 4] (by decide) (by decide)
theorem cert4_2_7 : Range12 d4_2_7 → ∃ i, Equivalent d4_2_7 (fourReps i) := by
  intro _
  refine ⟨2, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨0, false, by decide⟩
def d4_2_8 : Diagram 4 := tableDiagram (by decide) [3, 5, 7, 0, 6, 1, 4, 2] (by decide) (by decide)
theorem cert4_2_8 : Range12 d4_2_8 → ∃ i, Equivalent d4_2_8 (fourReps i) := by
  intro _
  refine ⟨1, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨4, false, by decide⟩
def d4_2_9 : Diagram 4 := tableDiagram (by decide) [3, 6, 4, 0, 2, 7, 1, 5] (by decide) (by decide)
theorem cert4_2_9 : Range12 d4_2_9 → ∃ i, Equivalent d4_2_9 (fourReps i) := by
  intro h
  have hg : genusRange d4_2_9 0 := ⟨maskSides 4 86, by decide⟩
  have := (h 0).mp hg
  omega
def d4_2_10 : Diagram 4 := tableDiagram (by decide) [3, 6, 5, 0, 7, 2, 1, 4] (by decide) (by decide)
theorem cert4_2_10 : Range12 d4_2_10 → ∃ i, Equivalent d4_2_10 (fourReps i) := by
  intro h
  have hg : genusRange d4_2_10 0 := ⟨maskSides 4 102, by decide⟩
  have := (h 0).mp hg
  omega
def d4_2_11 : Diagram 4 := tableDiagram (by decide) [3, 6, 7, 0, 5, 4, 1, 2] (by decide) (by decide)
theorem cert4_2_11 : Range12 d4_2_11 → ∃ i, Equivalent d4_2_11 (fourReps i) := by
  intro _
  refine ⟨0, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩
  exact ⟨4, false, by decide⟩
def d4_2_12 : Diagram 4 := tableDiagram (by decide) [3, 7, 4, 0, 2, 6, 5, 1] (by decide) (by decide)
theorem cert4_2_12 : Range12 d4_2_12 → ∃ i, Equivalent d4_2_12 (fourReps i) := by
  intro h
  have hg : genusRange d4_2_12 0 := ⟨maskSides 4 9, by decide⟩
  have := (h 0).mp hg
  omega
def d4_2_13 : Diagram 4 := tableDiagram (by decide) [3, 7, 5, 0, 6, 2, 4, 1] (by decide) (by decide)
theorem cert4_2_13 : Range12 d4_2_13 → ∃ i, Equivalent d4_2_13 (fourReps i) := by
  intro h
  have hg : genusRange d4_2_13 0 := ⟨maskSides 4 89, by decide⟩
  have := (h 0).mp hg
  omega
def d4_2_14 : Diagram 4 := tableDiagram (by decide) [3, 7, 6, 0, 5, 4, 2, 1] (by decide) (by decide)
theorem cert4_2_14 : Range12 d4_2_14 → ∃ i, Equivalent d4_2_14 (fourReps i) := by
  intro h
  have hg : genusRange d4_2_14 0 := ⟨maskSides 4 9, by decide⟩
  have := (h 0).mp hg
  omega
theorem cases4_2 (P : Diagram 4 → Prop)
    (c0 : P d4_2_0)
    (c1 : P d4_2_1)
    (c2 : P d4_2_2)
    (c3 : P d4_2_3)
    (c4 : P d4_2_4)
    (c5 : P d4_2_5)
    (c6 : P d4_2_6)
    (c7 : P d4_2_7)
    (c8 : P d4_2_8)
    (c9 : P d4_2_9)
    (c10 : P d4_2_10)
    (c11 : P d4_2_11)
    (c12 : P d4_2_12)
    (c13 : P d4_2_13)
    (c14 : P d4_2_14)
    (D : Diagram 4) (h0 : D.partner 0 = 3) (h3 : D.partner 3 = 0) : P D := by
  have opts : D.partner 1 = 2 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 ∨ D.partner 1 = 6 ∨ D.partner 1 = 7 := by
    have inv := D.involutive 1
    have nf := D.noFixed 1
    generalize hv : D.partner 1 = v
    fin_cases v <;> simp_all
  rcases opts with h1_2 | h1_4 | h1_5 | h1_6 | h1_7
  · have h2 : D.partner 2 = 1 := by simpa only [h1_2] using D.involutive 1
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
      have hd : D = d4_2_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_2_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_2_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h4 : D.partner 4 = 1 := by simpa only [h1_4] using D.involutive 1
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
      have hd : D = d4_2_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d4_2_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_2_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h5 : D.partner 5 = 1 := by simpa only [h1_5] using D.involutive 1
    have opts : D.partner 2 = 4 ∨ D.partner 2 = 6 ∨ D.partner 2 = 7 := by
      have inv := D.involutive 2
      have nf := D.noFixed 2
      generalize hv : D.partner 2 = v
      fin_cases v <;> simp_all
    rcases opts with h2_4 | h2_6 | h2_7
    · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d4_2_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d4_2_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
      have opts : D.partner 4 = 6 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_6 := opts
      have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have hd : D = d4_2_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h6 : D.partner 6 = 1 := by simpa only [h1_6] using D.involutive 1
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
      have hd : D = d4_2_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d4_2_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d4_2_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h7 : D.partner 7 = 1 := by simpa only [h1_7] using D.involutive 1
    have opts : D.partner 2 = 4 ∨ D.partner 2 = 5 ∨ D.partner 2 = 6 := by
      have inv := D.involutive 2
      have nf := D.noFixed 2
      generalize hv : D.partner 2 = v
      fin_cases v <;> simp_all
    rcases opts with h2_4 | h2_5 | h2_6
    · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d4_2_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have opts : D.partner 4 = 6 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_6 := opts
      have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have hd : D = d4_2_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d4_2_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d4_2_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed4_2 (D : Diagram 4) (h0 : D.partner 0 = 3) (h3 : D.partner 3 = 0) : Range12 D → ∃ i, Equivalent D (fourReps i) :=
  cases4_2 (fun E => Range12 E → ∃ i, Equivalent E (fourReps i)) cert4_2_0 cert4_2_1 cert4_2_2 cert4_2_3 cert4_2_4 cert4_2_5 cert4_2_6 cert4_2_7 cert4_2_8 cert4_2_9 cert4_2_10 cert4_2_11 cert4_2_12 cert4_2_13 cert4_2_14 D h0 h3
end Chord.Comb2
