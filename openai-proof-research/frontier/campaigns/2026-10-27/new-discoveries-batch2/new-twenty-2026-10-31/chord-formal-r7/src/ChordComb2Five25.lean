import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d5_25_0 : Diagram 5 := tableDiagram (by decide) [4, 7, 3, 2, 0, 6, 5, 1, 9, 8] (by decide) (by decide)
theorem cert5_25_0 : MaxTwo d5_25_0 → FiveProperty d5_25_0 := by
  intro _
  constructor
  · exact ⟨2, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_25_0) h)
def d5_25_1 : Diagram 5 := tableDiagram (by decide) [4, 7, 3, 2, 0, 8, 9, 1, 5, 6] (by decide) (by decide)
theorem cert5_25_1 : MaxTwo d5_25_1 → FiveProperty d5_25_1 := by
  intro h
  have hg : genusRange d5_25_1 3 := ⟨maskSides5 4, by decide⟩
  have := h 3 hg
  omega
def d5_25_2 : Diagram 5 := tableDiagram (by decide) [4, 7, 3, 2, 0, 9, 8, 1, 6, 5] (by decide) (by decide)
theorem cert5_25_2 : MaxTwo d5_25_2 → FiveProperty d5_25_2 := by
  intro _
  constructor
  · exact ⟨2, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_25_2) h)
def d5_25_3 : Diagram 5 := tableDiagram (by decide) [4, 7, 5, 6, 0, 2, 3, 1, 9, 8] (by decide) (by decide)
theorem cert5_25_3 : MaxTwo d5_25_3 → FiveProperty d5_25_3 := by
  intro h
  have hg : genusRange d5_25_3 3 := ⟨maskSides5 256, by decide⟩
  have := h 3 hg
  omega
def d5_25_4 : Diagram 5 := tableDiagram (by decide) [4, 7, 5, 8, 0, 2, 9, 1, 3, 6] (by decide) (by decide)
theorem cert5_25_4 : MaxTwo d5_25_4 → FiveProperty d5_25_4 := by
  intro h
  have hg : genusRange d5_25_4 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_25_5 : Diagram 5 := tableDiagram (by decide) [4, 7, 5, 9, 0, 2, 8, 1, 6, 3] (by decide) (by decide)
theorem cert5_25_5 : MaxTwo d5_25_5 → FiveProperty d5_25_5 := by
  intro h
  have hg : genusRange d5_25_5 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_25_6 : Diagram 5 := tableDiagram (by decide) [4, 7, 6, 5, 0, 3, 2, 1, 9, 8] (by decide) (by decide)
theorem cert5_25_6 : MaxTwo d5_25_6 → FiveProperty d5_25_6 := by
  intro _
  constructor
  · exact ⟨8, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_25_6) h)
def d5_25_7 : Diagram 5 := tableDiagram (by decide) [4, 7, 6, 8, 0, 9, 2, 1, 3, 5] (by decide) (by decide)
theorem cert5_25_7 : MaxTwo d5_25_7 → FiveProperty d5_25_7 := by
  intro h
  have hg : genusRange d5_25_7 3 := ⟨maskSides5 5, by decide⟩
  have := h 3 hg
  omega
def d5_25_8 : Diagram 5 := tableDiagram (by decide) [4, 7, 6, 9, 0, 8, 2, 1, 5, 3] (by decide) (by decide)
theorem cert5_25_8 : MaxTwo d5_25_8 → FiveProperty d5_25_8 := by
  intro h
  have hg : genusRange d5_25_8 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_25_9 : Diagram 5 := tableDiagram (by decide) [4, 7, 8, 5, 0, 3, 9, 1, 2, 6] (by decide) (by decide)
theorem cert5_25_9 : MaxTwo d5_25_9 → FiveProperty d5_25_9 := by
  intro h
  have hg : genusRange d5_25_9 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_25_10 : Diagram 5 := tableDiagram (by decide) [4, 7, 8, 6, 0, 9, 3, 1, 2, 5] (by decide) (by decide)
theorem cert5_25_10 : MaxTwo d5_25_10 → FiveProperty d5_25_10 := by
  intro h
  have hg : genusRange d5_25_10 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_25_11 : Diagram 5 := tableDiagram (by decide) [4, 7, 8, 9, 0, 6, 5, 1, 2, 3] (by decide) (by decide)
theorem cert5_25_11 : MaxTwo d5_25_11 → FiveProperty d5_25_11 := by
  intro h
  have hg : genusRange d5_25_11 3 := ⟨maskSides5 32, by decide⟩
  have := h 3 hg
  omega
def d5_25_12 : Diagram 5 := tableDiagram (by decide) [4, 7, 9, 5, 0, 3, 8, 1, 6, 2] (by decide) (by decide)
theorem cert5_25_12 : MaxTwo d5_25_12 → FiveProperty d5_25_12 := by
  intro h
  have hg : genusRange d5_25_12 3 := ⟨maskSides5 4, by decide⟩
  have := h 3 hg
  omega
def d5_25_13 : Diagram 5 := tableDiagram (by decide) [4, 7, 9, 6, 0, 8, 3, 1, 5, 2] (by decide) (by decide)
theorem cert5_25_13 : MaxTwo d5_25_13 → FiveProperty d5_25_13 := by
  intro h
  have hg : genusRange d5_25_13 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_25_14 : Diagram 5 := tableDiagram (by decide) [4, 7, 9, 8, 0, 6, 5, 1, 3, 2] (by decide) (by decide)
theorem cert5_25_14 : MaxTwo d5_25_14 → FiveProperty d5_25_14 := by
  intro h
  have hg : genusRange d5_25_14 3 := ⟨maskSides5 37, by decide⟩
  have := h 3 hg
  omega
theorem cases5_25 (P : Diagram 5 → Prop)
    (c0 : P d5_25_0)
    (c1 : P d5_25_1)
    (c2 : P d5_25_2)
    (c3 : P d5_25_3)
    (c4 : P d5_25_4)
    (c5 : P d5_25_5)
    (c6 : P d5_25_6)
    (c7 : P d5_25_7)
    (c8 : P d5_25_8)
    (c9 : P d5_25_9)
    (c10 : P d5_25_10)
    (c11 : P d5_25_11)
    (c12 : P d5_25_12)
    (c13 : P d5_25_13)
    (c14 : P d5_25_14)
    (D : Diagram 5) (h0 : D.partner 0 = 4) (h4 : D.partner 4 = 0) (h1 : D.partner 1 = 7) (h7 : D.partner 7 = 1) : P D := by
  have opts : D.partner 2 = 3 ∨ D.partner 2 = 5 ∨ D.partner 2 = 6 ∨ D.partner 2 = 8 ∨ D.partner 2 = 9 := by
    have inv := D.involutive 2
    have nf := D.noFixed 2
    generalize hv : D.partner 2 = v
    fin_cases v <;> simp_all
  rcases opts with h2_3 | h2_5 | h2_6 | h2_8 | h2_9
  · have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
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
      have hd : D = d5_25_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_25_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_25_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
    have opts : D.partner 3 = 6 ∨ D.partner 3 = 8 ∨ D.partner 3 = 9 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_6 | h3_8 | h3_9
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 8 = 9 := by
        have inv := D.involutive 8
        have nf := D.noFixed 8
        generalize hv : D.partner 8 = v
        fin_cases v <;> simp_all
      have h8_9 := opts
      have h9 : D.partner 9 = 8 := by simpa only [h8_9] using D.involutive 8
      have hd : D = d5_25_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_25_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_25_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
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
      have hd : D = d5_25_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_25_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_25_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h8 : D.partner 8 = 2 := by simpa only [h2_8] using D.involutive 2
    have opts : D.partner 3 = 5 ∨ D.partner 3 = 6 ∨ D.partner 3 = 9 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_5 | h3_6 | h3_9
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_25_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_25_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_25_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h9 : D.partner 9 = 2 := by simpa only [h2_9] using D.involutive 2
    have opts : D.partner 3 = 5 ∨ D.partner 3 = 6 ∨ D.partner 3 = 8 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_5 | h3_6 | h3_8
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_25_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_25_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h8 : D.partner 8 = 3 := by simpa only [h3_8] using D.involutive 3
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_25_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_25_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed5_25 (D : Diagram 5) (h0 : D.partner 0 = 4) (h4 : D.partner 4 = 0) (h1 : D.partner 1 = 7) (h7 : D.partner 7 = 1) : MaxTwo D → FiveProperty D :=
  cases5_25 (fun E => MaxTwo E → FiveProperty E) cert5_25_0 cert5_25_1 cert5_25_2 cert5_25_3 cert5_25_4 cert5_25_5 cert5_25_6 cert5_25_7 cert5_25_8 cert5_25_9 cert5_25_10 cert5_25_11 cert5_25_12 cert5_25_13 cert5_25_14 D h0 h4 h1 h7
end Chord.Comb2
