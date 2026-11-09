import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d5_4_0 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 4, 3, 6, 5, 2, 9, 8] (by decide) (by decide)
theorem cert5_4_0 : MaxTwo d5_4_0 → FiveProperty d5_4_0 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_4_0) h)
def d5_4_1 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 4, 3, 8, 9, 2, 5, 6] (by decide) (by decide)
theorem cert5_4_1 : MaxTwo d5_4_1 → FiveProperty d5_4_1 := by
  intro h
  have hg : genusRange d5_4_1 3 := ⟨maskSides5 9, by decide⟩
  have := h 3 hg
  omega
def d5_4_2 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 4, 3, 9, 8, 2, 6, 5] (by decide) (by decide)
theorem cert5_4_2 : MaxTwo d5_4_2 → FiveProperty d5_4_2 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_4_2) h)
def d5_4_3 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 5, 6, 3, 4, 2, 9, 8] (by decide) (by decide)
theorem cert5_4_3 : MaxTwo d5_4_3 → FiveProperty d5_4_3 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_4_3) h)
def d5_4_4 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 5, 8, 3, 9, 2, 4, 6] (by decide) (by decide)
theorem cert5_4_4 : MaxTwo d5_4_4 → FiveProperty d5_4_4 := by
  intro h
  have hg : genusRange d5_4_4 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_4_5 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 5, 9, 3, 8, 2, 6, 4] (by decide) (by decide)
theorem cert5_4_5 : MaxTwo d5_4_5 → FiveProperty d5_4_5 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_4_5) h)
def d5_4_6 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 6, 5, 4, 3, 2, 9, 8] (by decide) (by decide)
theorem cert5_4_6 : MaxTwo d5_4_6 → FiveProperty d5_4_6 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_4_6) h)
def d5_4_7 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 6, 8, 9, 3, 2, 4, 5] (by decide) (by decide)
theorem cert5_4_7 : MaxTwo d5_4_7 → FiveProperty d5_4_7 := by
  intro h
  have hg : genusRange d5_4_7 3 := ⟨maskSides5 9, by decide⟩
  have := h 3 hg
  omega
def d5_4_8 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 6, 9, 8, 3, 2, 5, 4] (by decide) (by decide)
theorem cert5_4_8 : MaxTwo d5_4_8 → FiveProperty d5_4_8 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_4_8) h)
def d5_4_9 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 8, 5, 4, 9, 2, 3, 6] (by decide) (by decide)
theorem cert5_4_9 : MaxTwo d5_4_9 → FiveProperty d5_4_9 := by
  intro h
  have hg : genusRange d5_4_9 3 := ⟨maskSides5 145, by decide⟩
  have := h 3 hg
  omega
def d5_4_10 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 8, 6, 9, 4, 2, 3, 5] (by decide) (by decide)
theorem cert5_4_10 : MaxTwo d5_4_10 → FiveProperty d5_4_10 := by
  intro h
  have hg : genusRange d5_4_10 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_4_11 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 8, 9, 6, 5, 2, 3, 4] (by decide) (by decide)
theorem cert5_4_11 : MaxTwo d5_4_11 → FiveProperty d5_4_11 := by
  intro h
  have hg : genusRange d5_4_11 3 := ⟨maskSides5 33, by decide⟩
  have := h 3 hg
  omega
def d5_4_12 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 9, 5, 4, 8, 2, 6, 3] (by decide) (by decide)
theorem cert5_4_12 : MaxTwo d5_4_12 → FiveProperty d5_4_12 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_4_12) h)
def d5_4_13 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 9, 6, 8, 4, 2, 5, 3] (by decide) (by decide)
theorem cert5_4_13 : MaxTwo d5_4_13 → FiveProperty d5_4_13 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_4_13) h)
def d5_4_14 : Diagram 5 := tableDiagram (by decide) [1, 0, 7, 9, 8, 6, 5, 2, 4, 3] (by decide) (by decide)
theorem cert5_4_14 : MaxTwo d5_4_14 → FiveProperty d5_4_14 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_4_14) h)
theorem cases5_4 (P : Diagram 5 → Prop)
    (c0 : P d5_4_0)
    (c1 : P d5_4_1)
    (c2 : P d5_4_2)
    (c3 : P d5_4_3)
    (c4 : P d5_4_4)
    (c5 : P d5_4_5)
    (c6 : P d5_4_6)
    (c7 : P d5_4_7)
    (c8 : P d5_4_8)
    (c9 : P d5_4_9)
    (c10 : P d5_4_10)
    (c11 : P d5_4_11)
    (c12 : P d5_4_12)
    (c13 : P d5_4_13)
    (c14 : P d5_4_14)
    (D : Diagram 5) (h0 : D.partner 0 = 1) (h1 : D.partner 1 = 0) (h2 : D.partner 2 = 7) (h7 : D.partner 7 = 2) : P D := by
  have opts : D.partner 3 = 4 ∨ D.partner 3 = 5 ∨ D.partner 3 = 6 ∨ D.partner 3 = 8 ∨ D.partner 3 = 9 := by
    have inv := D.involutive 3
    have nf := D.noFixed 3
    generalize hv : D.partner 3 = v
    fin_cases v <;> simp_all
  rcases opts with h3_4 | h3_5 | h3_6 | h3_8 | h3_9
  · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
    have opts : D.partner 5 = 6 ∨ D.partner 5 = 8 ∨ D.partner 5 = 9 := by
      have inv := D.involutive 5
      have nf := D.noFixed 5
      generalize hv : D.partner 5 = v
      fin_cases v <;> simp_all
    rcases opts with h5_6 | h5_8 | h5_9
    · have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have opts : D.partner 8 = 9 := by
        have inv := D.involutive 8
        have nf := D.noFixed 8
        generalize hv : D.partner 8 = v
        fin_cases v <;> simp_all
      have h8_9 := opts
      have h9 : D.partner 9 = 8 := by simpa only [h8_9] using D.involutive 8
      have hd : D = d5_4_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_4_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_4_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
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
      have hd : D = d5_4_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_4_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_4_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
    have opts : D.partner 4 = 5 ∨ D.partner 4 = 8 ∨ D.partner 4 = 9 := by
      have inv := D.involutive 4
      have nf := D.noFixed 4
      generalize hv : D.partner 4 = v
      fin_cases v <;> simp_all
    rcases opts with h4_5 | h4_8 | h4_9
    · have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have opts : D.partner 8 = 9 := by
        have inv := D.involutive 8
        have nf := D.noFixed 8
        generalize hv : D.partner 8 = v
        fin_cases v <;> simp_all
      have h8_9 := opts
      have h9 : D.partner 9 = 8 := by simpa only [h8_9] using D.involutive 8
      have hd : D = d5_4_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_4_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_4_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
    have opts : D.partner 4 = 5 ∨ D.partner 4 = 6 ∨ D.partner 4 = 9 := by
      have inv := D.involutive 4
      have nf := D.noFixed 4
      generalize hv : D.partner 4 = v
      fin_cases v <;> simp_all
    rcases opts with h4_5 | h4_6 | h4_9
    · have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_4_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_4_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_4_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
    have opts : D.partner 4 = 5 ∨ D.partner 4 = 6 ∨ D.partner 4 = 8 := by
      have inv := D.involutive 4
      have nf := D.noFixed 4
      generalize hv : D.partner 4 = v
      fin_cases v <;> simp_all
    rcases opts with h4_5 | h4_6 | h4_8
    · have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_4_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_4_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_4_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_4_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed5_4 (D : Diagram 5) (h0 : D.partner 0 = 1) (h1 : D.partner 1 = 0) (h2 : D.partner 2 = 7) (h7 : D.partner 7 = 2) : MaxTwo D → FiveProperty D :=
  cases5_4 (fun E => MaxTwo E → FiveProperty E) cert5_4_0 cert5_4_1 cert5_4_2 cert5_4_3 cert5_4_4 cert5_4_5 cert5_4_6 cert5_4_7 cert5_4_8 cert5_4_9 cert5_4_10 cert5_4_11 cert5_4_12 cert5_4_13 cert5_4_14 D h0 h1 h2 h7
end Chord.Comb2
