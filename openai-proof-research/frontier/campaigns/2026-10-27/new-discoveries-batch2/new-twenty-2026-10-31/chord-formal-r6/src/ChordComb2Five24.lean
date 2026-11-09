import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d5_24_0 : Diagram 5 := tableDiagram (by decide) [4, 6, 3, 2, 0, 7, 1, 5, 9, 8] (by decide) (by decide)
theorem cert5_24_0 : MaxTwo d5_24_0 → FiveProperty d5_24_0 := by
  intro _
  constructor
  · exact ⟨2, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_24_0) h)
def d5_24_1 : Diagram 5 := tableDiagram (by decide) [4, 6, 3, 2, 0, 8, 1, 9, 5, 7] (by decide) (by decide)
theorem cert5_24_1 : MaxTwo d5_24_1 → FiveProperty d5_24_1 := by
  intro _
  constructor
  · exact ⟨2, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_24_1) h)
def d5_24_2 : Diagram 5 := tableDiagram (by decide) [4, 6, 3, 2, 0, 9, 1, 8, 7, 5] (by decide) (by decide)
theorem cert5_24_2 : MaxTwo d5_24_2 → FiveProperty d5_24_2 := by
  intro _
  constructor
  · exact ⟨2, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_24_2) h)
def d5_24_3 : Diagram 5 := tableDiagram (by decide) [4, 6, 5, 7, 0, 2, 1, 3, 9, 8] (by decide) (by decide)
theorem cert5_24_3 : MaxTwo d5_24_3 → FiveProperty d5_24_3 := by
  intro h
  have hg : genusRange d5_24_3 3 := ⟨maskSides5 258, by decide⟩
  have := h 3 hg
  omega
def d5_24_4 : Diagram 5 := tableDiagram (by decide) [4, 6, 5, 8, 0, 2, 1, 9, 3, 7] (by decide) (by decide)
theorem cert5_24_4 : MaxTwo d5_24_4 → FiveProperty d5_24_4 := by
  intro h
  have hg : genusRange d5_24_4 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_24_5 : Diagram 5 := tableDiagram (by decide) [4, 6, 5, 9, 0, 2, 1, 8, 7, 3] (by decide) (by decide)
theorem cert5_24_5 : MaxTwo d5_24_5 → FiveProperty d5_24_5 := by
  intro h
  have hg : genusRange d5_24_5 3 := ⟨maskSides5 132, by decide⟩
  have := h 3 hg
  omega
def d5_24_6 : Diagram 5 := tableDiagram (by decide) [4, 6, 7, 5, 0, 3, 1, 2, 9, 8] (by decide) (by decide)
theorem cert5_24_6 : MaxTwo d5_24_6 → FiveProperty d5_24_6 := by
  intro h
  have hg : genusRange d5_24_6 3 := ⟨maskSides5 256, by decide⟩
  have := h 3 hg
  omega
def d5_24_7 : Diagram 5 := tableDiagram (by decide) [4, 6, 7, 8, 0, 9, 1, 2, 3, 5] (by decide) (by decide)
theorem cert5_24_7 : MaxTwo d5_24_7 → FiveProperty d5_24_7 := by
  intro h
  have hg : genusRange d5_24_7 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_24_8 : Diagram 5 := tableDiagram (by decide) [4, 6, 7, 9, 0, 8, 1, 2, 5, 3] (by decide) (by decide)
theorem cert5_24_8 : MaxTwo d5_24_8 → FiveProperty d5_24_8 := by
  intro h
  have hg : genusRange d5_24_8 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_24_9 : Diagram 5 := tableDiagram (by decide) [4, 6, 8, 5, 0, 3, 1, 9, 2, 7] (by decide) (by decide)
theorem cert5_24_9 : MaxTwo d5_24_9 → FiveProperty d5_24_9 := by
  intro h
  have hg : genusRange d5_24_9 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_24_10 : Diagram 5 := tableDiagram (by decide) [4, 6, 8, 7, 0, 9, 1, 3, 2, 5] (by decide) (by decide)
theorem cert5_24_10 : MaxTwo d5_24_10 → FiveProperty d5_24_10 := by
  intro h
  have hg : genusRange d5_24_10 3 := ⟨maskSides5 5, by decide⟩
  have := h 3 hg
  omega
def d5_24_11 : Diagram 5 := tableDiagram (by decide) [4, 6, 8, 9, 0, 7, 1, 5, 2, 3] (by decide) (by decide)
theorem cert5_24_11 : MaxTwo d5_24_11 → FiveProperty d5_24_11 := by
  intro h
  have hg : genusRange d5_24_11 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_24_12 : Diagram 5 := tableDiagram (by decide) [4, 6, 9, 5, 0, 3, 1, 8, 7, 2] (by decide) (by decide)
theorem cert5_24_12 : MaxTwo d5_24_12 → FiveProperty d5_24_12 := by
  intro h
  have hg : genusRange d5_24_12 3 := ⟨maskSides5 128, by decide⟩
  have := h 3 hg
  omega
def d5_24_13 : Diagram 5 := tableDiagram (by decide) [4, 6, 9, 7, 0, 8, 1, 3, 5, 2] (by decide) (by decide)
theorem cert5_24_13 : MaxTwo d5_24_13 → FiveProperty d5_24_13 := by
  intro h
  have hg : genusRange d5_24_13 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_24_14 : Diagram 5 := tableDiagram (by decide) [4, 6, 9, 8, 0, 7, 1, 5, 3, 2] (by decide) (by decide)
theorem cert5_24_14 : MaxTwo d5_24_14 → FiveProperty d5_24_14 := by
  intro h
  have hg : genusRange d5_24_14 3 := ⟨maskSides5 4, by decide⟩
  have := h 3 hg
  omega
theorem cases5_24 (P : Diagram 5 → Prop)
    (c0 : P d5_24_0)
    (c1 : P d5_24_1)
    (c2 : P d5_24_2)
    (c3 : P d5_24_3)
    (c4 : P d5_24_4)
    (c5 : P d5_24_5)
    (c6 : P d5_24_6)
    (c7 : P d5_24_7)
    (c8 : P d5_24_8)
    (c9 : P d5_24_9)
    (c10 : P d5_24_10)
    (c11 : P d5_24_11)
    (c12 : P d5_24_12)
    (c13 : P d5_24_13)
    (c14 : P d5_24_14)
    (D : Diagram 5) (h0 : D.partner 0 = 4) (h4 : D.partner 4 = 0) (h1 : D.partner 1 = 6) (h6 : D.partner 6 = 1) : P D := by
  have opts : D.partner 2 = 3 ∨ D.partner 2 = 5 ∨ D.partner 2 = 7 ∨ D.partner 2 = 8 ∨ D.partner 2 = 9 := by
    have inv := D.involutive 2
    have nf := D.noFixed 2
    generalize hv : D.partner 2 = v
    fin_cases v <;> simp_all
  rcases opts with h2_3 | h2_5 | h2_7 | h2_8 | h2_9
  · have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
    have opts : D.partner 5 = 7 ∨ D.partner 5 = 8 ∨ D.partner 5 = 9 := by
      have inv := D.involutive 5
      have nf := D.noFixed 5
      generalize hv : D.partner 5 = v
      fin_cases v <;> simp_all
    rcases opts with h5_7 | h5_8 | h5_9
    · have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have opts : D.partner 8 = 9 := by
        have inv := D.involutive 8
        have nf := D.noFixed 8
        generalize hv : D.partner 8 = v
        fin_cases v <;> simp_all
      have h8_9 := opts
      have h9 : D.partner 9 = 8 := by simpa only [h8_9] using D.involutive 8
      have hd : D = d5_24_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have opts : D.partner 7 = 9 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_9 := opts
      have h9 : D.partner 9 = 7 := by simpa only [h7_9] using D.involutive 7
      have hd : D = d5_24_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_24_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
    have opts : D.partner 3 = 7 ∨ D.partner 3 = 8 ∨ D.partner 3 = 9 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_7 | h3_8 | h3_9
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 8 = 9 := by
        have inv := D.involutive 8
        have nf := D.noFixed 8
        generalize hv : D.partner 8 = v
        fin_cases v <;> simp_all
      have h8_9 := opts
      have h9 : D.partner 9 = 8 := by simpa only [h8_9] using D.involutive 8
      have hd : D = d5_24_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
      have opts : D.partner 7 = 9 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_9 := opts
      have h9 : D.partner 9 = 7 := by simpa only [h7_9] using D.involutive 7
      have hd : D = d5_24_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_24_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
    have opts : D.partner 3 = 5 ∨ D.partner 3 = 8 ∨ D.partner 3 = 9 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_5 | h3_8 | h3_9
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 8 = 9 := by
        have inv := D.involutive 8
        have nf := D.noFixed 8
        generalize hv : D.partner 8 = v
        fin_cases v <;> simp_all
      have h8_9 := opts
      have h9 : D.partner 9 = 8 := by simpa only [h8_9] using D.involutive 8
      have hd : D = d5_24_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_24_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_24_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h8 : D.partner 8 = 2 := by simpa only [h2_8] using D.involutive 2
    have opts : D.partner 3 = 5 ∨ D.partner 3 = 7 ∨ D.partner 3 = 9 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_5 | h3_7 | h3_9
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 7 = 9 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_9 := opts
      have h9 : D.partner 9 = 7 := by simpa only [h7_9] using D.involutive 7
      have hd : D = d5_24_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_24_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d5_24_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h9 : D.partner 9 = 2 := by simpa only [h2_9] using D.involutive 2
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
      have hd : D = d5_24_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_24_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d5_24_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_24_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed5_24 (D : Diagram 5) (h0 : D.partner 0 = 4) (h4 : D.partner 4 = 0) (h1 : D.partner 1 = 6) (h6 : D.partner 6 = 1) : MaxTwo D → FiveProperty D :=
  cases5_24 (fun E => MaxTwo E → FiveProperty E) cert5_24_0 cert5_24_1 cert5_24_2 cert5_24_3 cert5_24_4 cert5_24_5 cert5_24_6 cert5_24_7 cert5_24_8 cert5_24_9 cert5_24_10 cert5_24_11 cert5_24_12 cert5_24_13 cert5_24_14 D h0 h4 h1 h6
end Chord.Comb2
