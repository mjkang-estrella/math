import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d3_0 : Diagram 3 := tableDiagram (by decide) [1, 0, 3, 2, 5, 4] (by decide) (by decide)
theorem tri3_0 : HasTriangle d3_0 → d3_0 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_0) h)
def d3_1 : Diagram 3 := tableDiagram (by decide) [1, 0, 4, 5, 2, 3] (by decide) (by decide)
theorem tri3_1 : HasTriangle d3_1 → d3_1 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_1) h)
def d3_2 : Diagram 3 := tableDiagram (by decide) [1, 0, 5, 4, 3, 2] (by decide) (by decide)
theorem tri3_2 : HasTriangle d3_2 → d3_2 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_2) h)
def d3_3 : Diagram 3 := tableDiagram (by decide) [2, 3, 0, 1, 5, 4] (by decide) (by decide)
theorem tri3_3 : HasTriangle d3_3 → d3_3 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_3) h)
def d3_4 : Diagram 3 := tableDiagram (by decide) [2, 4, 0, 5, 1, 3] (by decide) (by decide)
theorem tri3_4 : HasTriangle d3_4 → d3_4 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_4) h)
def d3_5 : Diagram 3 := tableDiagram (by decide) [2, 5, 0, 4, 3, 1] (by decide) (by decide)
theorem tri3_5 : HasTriangle d3_5 → d3_5 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_5) h)
def d3_6 : Diagram 3 := tableDiagram (by decide) [3, 2, 1, 0, 5, 4] (by decide) (by decide)
theorem tri3_6 : HasTriangle d3_6 → d3_6 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_6) h)
def d3_7 : Diagram 3 := tableDiagram (by decide) [3, 4, 5, 0, 1, 2] (by decide) (by decide)
theorem tri3_7 : HasTriangle d3_7 → d3_7 = r3Block 3 (by decide) := by
  intro _
  apply diagram_ext
  decide
def d3_8 : Diagram 3 := tableDiagram (by decide) [3, 5, 4, 0, 2, 1] (by decide) (by decide)
theorem tri3_8 : HasTriangle d3_8 → d3_8 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_8) h)
def d3_9 : Diagram 3 := tableDiagram (by decide) [4, 2, 1, 5, 0, 3] (by decide) (by decide)
theorem tri3_9 : HasTriangle d3_9 → d3_9 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_9) h)
def d3_10 : Diagram 3 := tableDiagram (by decide) [4, 3, 5, 1, 0, 2] (by decide) (by decide)
theorem tri3_10 : HasTriangle d3_10 → d3_10 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_10) h)
def d3_11 : Diagram 3 := tableDiagram (by decide) [4, 5, 3, 2, 0, 1] (by decide) (by decide)
theorem tri3_11 : HasTriangle d3_11 → d3_11 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_11) h)
def d3_12 : Diagram 3 := tableDiagram (by decide) [5, 2, 1, 4, 3, 0] (by decide) (by decide)
theorem tri3_12 : HasTriangle d3_12 → d3_12 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_12) h)
def d3_13 : Diagram 3 := tableDiagram (by decide) [5, 3, 4, 1, 2, 0] (by decide) (by decide)
theorem tri3_13 : HasTriangle d3_13 → d3_13 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_13) h)
def d3_14 : Diagram 3 := tableDiagram (by decide) [5, 4, 3, 2, 1, 0] (by decide) (by decide)
theorem tri3_14 : HasTriangle d3_14 → d3_14 = r3Block 3 (by decide) := by
  intro h
  exact False.elim ((by decide : ¬HasTriangle d3_14) h)
theorem cases3 (P : Diagram 3 → Prop)
    (c0 : P d3_0)
    (c1 : P d3_1)
    (c2 : P d3_2)
    (c3 : P d3_3)
    (c4 : P d3_4)
    (c5 : P d3_5)
    (c6 : P d3_6)
    (c7 : P d3_7)
    (c8 : P d3_8)
    (c9 : P d3_9)
    (c10 : P d3_10)
    (c11 : P d3_11)
    (c12 : P d3_12)
    (c13 : P d3_13)
    (c14 : P d3_14)
    (D : Diagram 3) : P D := by
  have opts : D.partner 0 = 1 ∨ D.partner 0 = 2 ∨ D.partner 0 = 3 ∨ D.partner 0 = 4 ∨ D.partner 0 = 5 := by
    have inv := D.involutive 0
    have nf := D.noFixed 0
    generalize hv : D.partner 0 = v
    fin_cases v <;> simp_all
  rcases opts with h0_1 | h0_2 | h0_3 | h0_4 | h0_5
  · have h1 : D.partner 1 = 0 := by simpa only [h0_1] using D.involutive 0
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
      have hd : D = d3_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
      have opts : D.partner 3 = 5 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_5 := opts
      have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have hd : D = d3_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have opts : D.partner 3 = 4 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_4 := opts
      have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have hd : D = d3_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h2 : D.partner 2 = 0 := by simpa only [h0_2] using D.involutive 0
    have opts : D.partner 1 = 3 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_3 | h1_4 | h1_5
    · have h3 : D.partner 3 = 1 := by simpa only [h1_3] using D.involutive 1
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d3_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h4 : D.partner 4 = 1 := by simpa only [h1_4] using D.involutive 1
      have opts : D.partner 3 = 5 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_5 := opts
      have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have hd : D = d3_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h5 : D.partner 5 = 1 := by simpa only [h1_5] using D.involutive 1
      have opts : D.partner 3 = 4 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_4 := opts
      have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have hd : D = d3_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h3 : D.partner 3 = 0 := by simpa only [h0_3] using D.involutive 0
    have opts : D.partner 1 = 2 ∨ D.partner 1 = 4 ∨ D.partner 1 = 5 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_2 | h1_4 | h1_5
    · have h2 : D.partner 2 = 1 := by simpa only [h1_2] using D.involutive 1
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d3_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h4 : D.partner 4 = 1 := by simpa only [h1_4] using D.involutive 1
      have opts : D.partner 2 = 5 := by
        have inv := D.involutive 2
        have nf := D.noFixed 2
        generalize hv : D.partner 2 = v
        fin_cases v <;> simp_all
      have h2_5 := opts
      have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have hd : D = d3_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h5 : D.partner 5 = 1 := by simpa only [h1_5] using D.involutive 1
      have opts : D.partner 2 = 4 := by
        have inv := D.involutive 2
        have nf := D.noFixed 2
        generalize hv : D.partner 2 = v
        fin_cases v <;> simp_all
      have h2_4 := opts
      have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
      have hd : D = d3_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h4 : D.partner 4 = 0 := by simpa only [h0_4] using D.involutive 0
    have opts : D.partner 1 = 2 ∨ D.partner 1 = 3 ∨ D.partner 1 = 5 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_2 | h1_3 | h1_5
    · have h2 : D.partner 2 = 1 := by simpa only [h1_2] using D.involutive 1
      have opts : D.partner 3 = 5 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_5 := opts
      have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have hd : D = d3_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h3 : D.partner 3 = 1 := by simpa only [h1_3] using D.involutive 1
      have opts : D.partner 2 = 5 := by
        have inv := D.involutive 2
        have nf := D.noFixed 2
        generalize hv : D.partner 2 = v
        fin_cases v <;> simp_all
      have h2_5 := opts
      have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
      have hd : D = d3_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h5 : D.partner 5 = 1 := by simpa only [h1_5] using D.involutive 1
      have opts : D.partner 2 = 3 := by
        have inv := D.involutive 2
        have nf := D.noFixed 2
        generalize hv : D.partner 2 = v
        fin_cases v <;> simp_all
      have h2_3 := opts
      have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
      have hd : D = d3_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h5 : D.partner 5 = 0 := by simpa only [h0_5] using D.involutive 0
    have opts : D.partner 1 = 2 ∨ D.partner 1 = 3 ∨ D.partner 1 = 4 := by
      have inv := D.involutive 1
      have nf := D.noFixed 1
      generalize hv : D.partner 1 = v
      fin_cases v <;> simp_all
    rcases opts with h1_2 | h1_3 | h1_4
    · have h2 : D.partner 2 = 1 := by simpa only [h1_2] using D.involutive 1
      have opts : D.partner 3 = 4 := by
        have inv := D.involutive 3
        have nf := D.noFixed 3
        generalize hv : D.partner 3 = v
        fin_cases v <;> simp_all
      have h3_4 := opts
      have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have hd : D = d3_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h3 : D.partner 3 = 1 := by simpa only [h1_3] using D.involutive 1
      have opts : D.partner 2 = 4 := by
        have inv := D.involutive 2
        have nf := D.noFixed 2
        generalize hv : D.partner 2 = v
        fin_cases v <;> simp_all
      have h2_4 := opts
      have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
      have hd : D = d3_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h4 : D.partner 4 = 1 := by simpa only [h1_4] using D.involutive 1
      have opts : D.partner 2 = 3 := by
        have inv := D.involutive 2
        have nf := D.noFixed 2
        generalize hv : D.partner 2 = v
        fin_cases v <;> simp_all
      have h2_3 := opts
      have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
      have hd : D = d3_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d3_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem triangle_three (D : Diagram 3) : HasTriangle D → D = r3Block 3 (by decide) :=
  cases3 (fun E => HasTriangle E → E = r3Block 3 (by decide)) tri3_0 tri3_1 tri3_2 tri3_3 tri3_4 tri3_5 tri3_6 tri3_7 tri3_8 tri3_9 tri3_10 tri3_11 tri3_12 tri3_13 tri3_14 D
theorem triangleRigidity_three (D : Diagram 3) (h : HasTriangle D) : Equivalent D (r3Block 3 (by decide)) := by
  rw [triangle_three D h]
  exact Relation.EqvGen.refl _
theorem range3_0 : Range12 d3_0 → d3_0 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_0 0 := ⟨maskSides 3 0, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_1 : Range12 d3_1 → d3_1 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_1 0 := ⟨maskSides 3 20, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_2 : Range12 d3_2 → d3_2 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_2 0 := ⟨maskSides 3 0, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_3 : Range12 d3_3 → d3_3 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_3 0 := ⟨maskSides 3 5, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_4 : Range12 d3_4 → d3_4 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_4 0 := ⟨maskSides 3 18, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_5 : Range12 d3_5 → d3_5 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_5 0 := ⟨maskSides 3 5, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_6 : Range12 d3_6 → d3_6 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_6 0 := ⟨maskSides 3 0, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_7 : Range12 d3_7 → d3_7 = r3Block 3 (by decide) := by
  intro _
  apply diagram_ext
  decide
theorem range3_8 : Range12 d3_8 → d3_8 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_8 0 := ⟨maskSides 3 9, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_9 : Range12 d3_9 → d3_9 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_9 0 := ⟨maskSides 3 17, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_10 : Range12 d3_10 → d3_10 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_10 0 := ⟨maskSides 3 27, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_11 : Range12 d3_11 → d3_11 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_11 0 := ⟨maskSides 3 17, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_12 : Range12 d3_12 → d3_12 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_12 0 := ⟨maskSides 3 0, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_13 : Range12 d3_13 → d3_13 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_13 0 := ⟨maskSides 3 10, by decide⟩
  have := (h 0).mp hg
  omega
theorem range3_14 : Range12 d3_14 → d3_14 = r3Block 3 (by decide) := by
  intro h
  have hg : genusRange d3_14 0 := ⟨maskSides 3 0, by decide⟩
  have := (h 0).mp hg
  omega
theorem range_three_complete (D : Diagram 3) : Range12 D → D = r3Block 3 (by decide) :=
  cases3 (fun E => Range12 E → E = r3Block 3 (by decide)) range3_0 range3_1 range3_2 range3_3 range3_4 range3_5 range3_6 range3_7 range3_8 range3_9 range3_10 range3_11 range3_12 range3_13 range3_14 D
theorem exactly_one_three : ExactlyClasses 3 1 := by
  refine ⟨fun _ => r3Block 3 (by decide), fun _ => genusRange_r3, ?_, ?_⟩
  · intro i j _
    exact Subsingleton.elim i j
  · intro D h
    refine ⟨0, ?_⟩
    rw [range_three_complete D h]
    exact Relation.EqvGen.refl _
end Chord.Comb2
