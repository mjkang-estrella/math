import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d5_28_0 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 4, 3, 0, 7, 6, 9, 8] (by decide) (by decide)
theorem cert5_28_0 : MaxTwo d5_28_0 → FiveProperty d5_28_0 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_28_0) h)
def d5_28_1 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 4, 3, 0, 8, 9, 6, 7] (by decide) (by decide)
theorem cert5_28_1 : MaxTwo d5_28_1 → FiveProperty d5_28_1 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_28_1) h)
def d5_28_2 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 4, 3, 0, 9, 8, 7, 6] (by decide) (by decide)
theorem cert5_28_2 : MaxTwo d5_28_2 → FiveProperty d5_28_2 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_28_2) h)
def d5_28_3 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 6, 7, 0, 3, 4, 9, 8] (by decide) (by decide)
theorem cert5_28_3 : MaxTwo d5_28_3 → FiveProperty d5_28_3 := by
  intro h
  have hg : genusRange d5_28_3 3 := ⟨maskSides5 258, by decide⟩
  have := h 3 hg
  omega
def d5_28_4 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 6, 8, 0, 3, 9, 4, 7] (by decide) (by decide)
theorem cert5_28_4 : MaxTwo d5_28_4 → FiveProperty d5_28_4 := by
  intro h
  have hg : genusRange d5_28_4 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_28_5 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 6, 9, 0, 3, 8, 7, 4] (by decide) (by decide)
theorem cert5_28_5 : MaxTwo d5_28_5 → FiveProperty d5_28_5 := by
  intro h
  have hg : genusRange d5_28_5 3 := ⟨maskSides5 146, by decide⟩
  have := h 3 hg
  omega
def d5_28_6 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 7, 6, 0, 4, 3, 9, 8] (by decide) (by decide)
theorem cert5_28_6 : MaxTwo d5_28_6 → FiveProperty d5_28_6 := by
  intro _
  constructor
  · exact ⟨1, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_28_6) h)
def d5_28_7 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 7, 8, 0, 9, 3, 4, 6] (by decide) (by decide)
theorem cert5_28_7 : MaxTwo d5_28_7 → FiveProperty d5_28_7 := by
  intro h
  have hg : genusRange d5_28_7 3 := ⟨maskSides5 66, by decide⟩
  have := h 3 hg
  omega
def d5_28_8 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 7, 9, 0, 8, 3, 6, 4] (by decide) (by decide)
theorem cert5_28_8 : MaxTwo d5_28_8 → FiveProperty d5_28_8 := by
  intro h
  have hg : genusRange d5_28_8 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_28_9 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 8, 6, 0, 4, 9, 3, 7] (by decide) (by decide)
theorem cert5_28_9 : MaxTwo d5_28_9 → FiveProperty d5_28_9 := by
  intro _
  constructor
  · exact ⟨1, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_28_9) h)
def d5_28_10 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 8, 7, 0, 9, 4, 3, 6] (by decide) (by decide)
theorem cert5_28_10 : MaxTwo d5_28_10 → FiveProperty d5_28_10 := by
  intro _
  constructor
  · exact ⟨1, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_28_10) h)
def d5_28_11 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 8, 9, 0, 7, 6, 3, 4] (by decide) (by decide)
theorem cert5_28_11 : MaxTwo d5_28_11 → FiveProperty d5_28_11 := by
  intro h
  have hg : genusRange d5_28_11 3 := ⟨maskSides5 66, by decide⟩
  have := h 3 hg
  omega
def d5_28_12 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 9, 6, 0, 4, 8, 7, 3] (by decide) (by decide)
theorem cert5_28_12 : MaxTwo d5_28_12 → FiveProperty d5_28_12 := by
  intro _
  constructor
  · exact ⟨1, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_28_12) h)
def d5_28_13 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 9, 7, 0, 8, 4, 6, 3] (by decide) (by decide)
theorem cert5_28_13 : MaxTwo d5_28_13 → FiveProperty d5_28_13 := by
  intro _
  constructor
  · exact ⟨1, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_28_13) h)
def d5_28_14 : Diagram 5 := tableDiagram (by decide) [5, 2, 1, 9, 8, 0, 7, 6, 4, 3] (by decide) (by decide)
theorem cert5_28_14 : MaxTwo d5_28_14 → FiveProperty d5_28_14 := by
  intro _
  constructor
  · exact ⟨1, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_28_14) h)
theorem cases5_28 (P : Diagram 5 → Prop)
    (c0 : P d5_28_0)
    (c1 : P d5_28_1)
    (c2 : P d5_28_2)
    (c3 : P d5_28_3)
    (c4 : P d5_28_4)
    (c5 : P d5_28_5)
    (c6 : P d5_28_6)
    (c7 : P d5_28_7)
    (c8 : P d5_28_8)
    (c9 : P d5_28_9)
    (c10 : P d5_28_10)
    (c11 : P d5_28_11)
    (c12 : P d5_28_12)
    (c13 : P d5_28_13)
    (c14 : P d5_28_14)
    (D : Diagram 5) (h0 : D.partner 0 = 5) (h5 : D.partner 5 = 0) (h1 : D.partner 1 = 2) (h2 : D.partner 2 = 1) : P D := by
  have opts : D.partner 3 = 4 ∨ D.partner 3 = 6 ∨ D.partner 3 = 7 ∨ D.partner 3 = 8 ∨ D.partner 3 = 9 := by
    have inv := D.involutive 3
    have nf := D.noFixed 3
    generalize hv : D.partner 3 = v
    fin_cases v <;> simp_all
  rcases opts with h3_4 | h3_6 | h3_7 | h3_8 | h3_9
  · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
    have opts : D.partner 6 = 7 ∨ D.partner 6 = 8 ∨ D.partner 6 = 9 := by
      have inv := D.involutive 6
      have nf := D.noFixed 6
      generalize hv : D.partner 6 = v
      fin_cases v <;> simp_all
    rcases opts with h6_7 | h6_8 | h6_9
    · have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have opts : D.partner 8 = 9 := by
        have inv := D.involutive 8
        have nf := D.noFixed 8
        generalize hv : D.partner 8 = v
        fin_cases v <;> simp_all
      have h8_9 := opts
      have h9 : D.partner 9 = 8 := by simpa only [h8_9] using D.involutive 8
      have hd : D = d5_28_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have opts : D.partner 7 = 9 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_9 := opts
      have h9 : D.partner 9 = 7 := by simpa only [h7_9] using D.involutive 7
      have hd : D = d5_28_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_28_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
    have opts : D.partner 4 = 7 ∨ D.partner 4 = 8 ∨ D.partner 4 = 9 := by
      have inv := D.involutive 4
      have nf := D.noFixed 4
      generalize hv : D.partner 4 = v
      fin_cases v <;> simp_all
    rcases opts with h4_7 | h4_8 | h4_9
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 8 = 9 := by
        have inv := D.involutive 8
        have nf := D.noFixed 8
        generalize hv : D.partner 8 = v
        fin_cases v <;> simp_all
      have h8_9 := opts
      have h9 : D.partner 9 = 8 := by simpa only [h8_9] using D.involutive 8
      have hd : D = d5_28_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 7 = 9 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_9 := opts
      have h9 : D.partner 9 = 7 := by simpa only [h7_9] using D.involutive 7
      have hd : D = d5_28_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_28_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
    have opts : D.partner 4 = 6 ∨ D.partner 4 = 8 ∨ D.partner 4 = 9 := by
      have inv := D.involutive 4
      have nf := D.noFixed 4
      generalize hv : D.partner 4 = v
      fin_cases v <;> simp_all
    rcases opts with h4_6 | h4_8 | h4_9
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 8 = 9 := by
        have inv := D.involutive 8
        have nf := D.noFixed 8
        generalize hv : D.partner 8 = v
        fin_cases v <;> simp_all
      have h8_9 := opts
      have h9 : D.partner 9 = 8 := by simpa only [h8_9] using D.involutive 8
      have hd : D = d5_28_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_28_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_28_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
    have opts : D.partner 4 = 6 ∨ D.partner 4 = 7 ∨ D.partner 4 = 9 := by
      have inv := D.involutive 4
      have nf := D.noFixed 4
      generalize hv : D.partner 4 = v
      fin_cases v <;> simp_all
    rcases opts with h4_6 | h4_7 | h4_9
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 7 = 9 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_9 := opts
      have h9 : D.partner 9 = 7 := by simpa only [h7_9] using D.involutive 7
      have hd : D = d5_28_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_28_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d5_28_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
    have opts : D.partner 4 = 6 ∨ D.partner 4 = 7 ∨ D.partner 4 = 8 := by
      have inv := D.involutive 4
      have nf := D.noFixed 4
      generalize hv : D.partner 4 = v
      fin_cases v <;> simp_all
    rcases opts with h4_6 | h4_7 | h4_8
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_28_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_28_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d5_28_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_28_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed5_28 (D : Diagram 5) (h0 : D.partner 0 = 5) (h5 : D.partner 5 = 0) (h1 : D.partner 1 = 2) (h2 : D.partner 2 = 1) : MaxTwo D → FiveProperty D :=
  cases5_28 (fun E => MaxTwo E → FiveProperty E) cert5_28_0 cert5_28_1 cert5_28_2 cert5_28_3 cert5_28_4 cert5_28_5 cert5_28_6 cert5_28_7 cert5_28_8 cert5_28_9 cert5_28_10 cert5_28_11 cert5_28_12 cert5_28_13 cert5_28_14 D h0 h5 h1 h2
end Chord.Comb2
