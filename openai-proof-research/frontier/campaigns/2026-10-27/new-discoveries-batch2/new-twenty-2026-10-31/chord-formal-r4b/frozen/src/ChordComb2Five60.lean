import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d5_60_0 : Diagram 5 := tableDiagram (by decide) [9, 6, 3, 2, 5, 4, 1, 8, 7, 0] (by decide) (by decide)
theorem cert5_60_0 : MaxTwo d5_60_0 → FiveProperty d5_60_0 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_60_0) h)
def d5_60_1 : Diagram 5 := tableDiagram (by decide) [9, 6, 3, 2, 7, 8, 1, 4, 5, 0] (by decide) (by decide)
theorem cert5_60_1 : MaxTwo d5_60_1 → FiveProperty d5_60_1 := by
  intro h
  have hg : genusRange d5_60_1 3 := ⟨maskSides5 5, by decide⟩
  have := h 3 hg
  omega
def d5_60_2 : Diagram 5 := tableDiagram (by decide) [9, 6, 3, 2, 8, 7, 1, 5, 4, 0] (by decide) (by decide)
theorem cert5_60_2 : MaxTwo d5_60_2 → FiveProperty d5_60_2 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_60_2) h)
def d5_60_3 : Diagram 5 := tableDiagram (by decide) [9, 6, 4, 5, 2, 3, 1, 8, 7, 0] (by decide) (by decide)
theorem cert5_60_3 : MaxTwo d5_60_3 → FiveProperty d5_60_3 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_60_3) h)
def d5_60_4 : Diagram 5 := tableDiagram (by decide) [9, 6, 4, 7, 2, 8, 1, 3, 5, 0] (by decide) (by decide)
theorem cert5_60_4 : MaxTwo d5_60_4 → FiveProperty d5_60_4 := by
  intro h
  have hg : genusRange d5_60_4 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_60_5 : Diagram 5 := tableDiagram (by decide) [9, 6, 4, 8, 2, 7, 1, 5, 3, 0] (by decide) (by decide)
theorem cert5_60_5 : MaxTwo d5_60_5 → FiveProperty d5_60_5 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_60_5) h)
def d5_60_6 : Diagram 5 := tableDiagram (by decide) [9, 6, 5, 4, 3, 2, 1, 8, 7, 0] (by decide) (by decide)
theorem cert5_60_6 : MaxTwo d5_60_6 → FiveProperty d5_60_6 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_60_6) h)
def d5_60_7 : Diagram 5 := tableDiagram (by decide) [9, 6, 5, 7, 8, 2, 1, 3, 4, 0] (by decide) (by decide)
theorem cert5_60_7 : MaxTwo d5_60_7 → FiveProperty d5_60_7 := by
  intro h
  have hg : genusRange d5_60_7 3 := ⟨maskSides5 5, by decide⟩
  have := h 3 hg
  omega
def d5_60_8 : Diagram 5 := tableDiagram (by decide) [9, 6, 5, 8, 7, 2, 1, 4, 3, 0] (by decide) (by decide)
theorem cert5_60_8 : MaxTwo d5_60_8 → FiveProperty d5_60_8 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_60_8) h)
def d5_60_9 : Diagram 5 := tableDiagram (by decide) [9, 6, 7, 4, 3, 8, 1, 2, 5, 0] (by decide) (by decide)
theorem cert5_60_9 : MaxTwo d5_60_9 → FiveProperty d5_60_9 := by
  intro h
  have hg : genusRange d5_60_9 3 := ⟨maskSides5 73, by decide⟩
  have := h 3 hg
  omega
def d5_60_10 : Diagram 5 := tableDiagram (by decide) [9, 6, 7, 5, 8, 3, 1, 2, 4, 0] (by decide) (by decide)
theorem cert5_60_10 : MaxTwo d5_60_10 → FiveProperty d5_60_10 := by
  intro h
  have hg : genusRange d5_60_10 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_60_11 : Diagram 5 := tableDiagram (by decide) [9, 6, 7, 8, 5, 4, 1, 2, 3, 0] (by decide) (by decide)
theorem cert5_60_11 : MaxTwo d5_60_11 → FiveProperty d5_60_11 := by
  intro h
  have hg : genusRange d5_60_11 3 := ⟨maskSides5 17, by decide⟩
  have := h 3 hg
  omega
def d5_60_12 : Diagram 5 := tableDiagram (by decide) [9, 6, 8, 4, 3, 7, 1, 5, 2, 0] (by decide) (by decide)
theorem cert5_60_12 : MaxTwo d5_60_12 → FiveProperty d5_60_12 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_60_12) h)
def d5_60_13 : Diagram 5 := tableDiagram (by decide) [9, 6, 8, 5, 7, 3, 1, 4, 2, 0] (by decide) (by decide)
theorem cert5_60_13 : MaxTwo d5_60_13 → FiveProperty d5_60_13 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_60_13) h)
def d5_60_14 : Diagram 5 := tableDiagram (by decide) [9, 6, 8, 7, 5, 4, 1, 3, 2, 0] (by decide) (by decide)
theorem cert5_60_14 : MaxTwo d5_60_14 → FiveProperty d5_60_14 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_60_14) h)
theorem cases5_60 (P : Diagram 5 → Prop)
    (c0 : P d5_60_0)
    (c1 : P d5_60_1)
    (c2 : P d5_60_2)
    (c3 : P d5_60_3)
    (c4 : P d5_60_4)
    (c5 : P d5_60_5)
    (c6 : P d5_60_6)
    (c7 : P d5_60_7)
    (c8 : P d5_60_8)
    (c9 : P d5_60_9)
    (c10 : P d5_60_10)
    (c11 : P d5_60_11)
    (c12 : P d5_60_12)
    (c13 : P d5_60_13)
    (c14 : P d5_60_14)
    (D : Diagram 5) (h0 : D.partner 0 = 9) (h9 : D.partner 9 = 0) (h1 : D.partner 1 = 6) (h6 : D.partner 6 = 1) : P D := by
  have opts : D.partner 2 = 3 ∨ D.partner 2 = 4 ∨ D.partner 2 = 5 ∨ D.partner 2 = 7 ∨ D.partner 2 = 8 := by
    have inv := D.involutive 2
    have nf := D.noFixed 2
    generalize hv : D.partner 2 = v
    fin_cases v <;> simp_all
  rcases opts with h2_3 | h2_4 | h2_5 | h2_7 | h2_8
  · have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
    have opts : D.partner 4 = 5 ∨ D.partner 4 = 7 ∨ D.partner 4 = 8 := by
      have inv := D.involutive 4
      have nf := D.noFixed 4
      generalize hv : D.partner 4 = v
      fin_cases v <;> simp_all
    rcases opts with h4_5 | h4_7 | h4_8
    · have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_60_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_60_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d5_60_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
    have opts : D.partner 3 = 5 ∨ D.partner 3 = 7 ∨ D.partner 3 = 8 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_5 | h3_7 | h3_8
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_60_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_60_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d5_60_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
    have opts : D.partner 3 = 4 ∨ D.partner 3 = 7 ∨ D.partner 3 = 8 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_4 | h3_7 | h3_8
    · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_60_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 4 = 8 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_8 := opts
      have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have hd : D = d5_60_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d5_60_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
    have opts : D.partner 3 = 4 ∨ D.partner 3 = 5 ∨ D.partner 3 = 8 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_4 | h3_5 | h3_8
    · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_60_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 4 = 8 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_8 := opts
      have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have hd : D = d5_60_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d5_60_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h8 : D.partner 8 = 2 := by simpa only [h2_8] using D.involutive 2
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
      have hd : D = d5_60_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 4 = 7 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_7 := opts
      have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have hd : D = d5_60_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d5_60_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_60_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed5_60 (D : Diagram 5) (h0 : D.partner 0 = 9) (h9 : D.partner 9 = 0) (h1 : D.partner 1 = 6) (h6 : D.partner 6 = 1) : MaxTwo D → FiveProperty D :=
  cases5_60 (fun E => MaxTwo E → FiveProperty E) cert5_60_0 cert5_60_1 cert5_60_2 cert5_60_3 cert5_60_4 cert5_60_5 cert5_60_6 cert5_60_7 cert5_60_8 cert5_60_9 cert5_60_10 cert5_60_11 cert5_60_12 cert5_60_13 cert5_60_14 D h0 h9 h1 h6
end Chord.Comb2
