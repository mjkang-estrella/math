import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d5_43_0 : Diagram 5 := tableDiagram (by decide) [7, 3, 4, 1, 2, 6, 5, 0, 9, 8] (by decide) (by decide)
theorem cert5_43_0 : MaxTwo d5_43_0 → FiveProperty d5_43_0 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_43_0) h)
def d5_43_1 : Diagram 5 := tableDiagram (by decide) [7, 3, 4, 1, 2, 8, 9, 0, 5, 6] (by decide) (by decide)
theorem cert5_43_1 : MaxTwo d5_43_1 → FiveProperty d5_43_1 := by
  intro h
  have hg : genusRange d5_43_1 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_43_2 : Diagram 5 := tableDiagram (by decide) [7, 3, 4, 1, 2, 9, 8, 0, 6, 5] (by decide) (by decide)
theorem cert5_43_2 : MaxTwo d5_43_2 → FiveProperty d5_43_2 := by
  intro h
  have hg : genusRange d5_43_2 3 := ⟨maskSides5 32, by decide⟩
  have := h 3 hg
  omega
def d5_43_3 : Diagram 5 := tableDiagram (by decide) [7, 3, 5, 1, 6, 2, 4, 0, 9, 8] (by decide) (by decide)
theorem cert5_43_3 : MaxTwo d5_43_3 → FiveProperty d5_43_3 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_43_3) h)
def d5_43_4 : Diagram 5 := tableDiagram (by decide) [7, 3, 5, 1, 8, 2, 9, 0, 4, 6] (by decide) (by decide)
theorem cert5_43_4 : MaxTwo d5_43_4 → FiveProperty d5_43_4 := by
  intro h
  have hg : genusRange d5_43_4 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_43_5 : Diagram 5 := tableDiagram (by decide) [7, 3, 5, 1, 9, 2, 8, 0, 6, 4] (by decide) (by decide)
theorem cert5_43_5 : MaxTwo d5_43_5 → FiveProperty d5_43_5 := by
  intro h
  have hg : genusRange d5_43_5 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_43_6 : Diagram 5 := tableDiagram (by decide) [7, 3, 6, 1, 5, 4, 2, 0, 9, 8] (by decide) (by decide)
theorem cert5_43_6 : MaxTwo d5_43_6 → FiveProperty d5_43_6 := by
  intro _
  constructor
  · exact ⟨0, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_43_6) h)
def d5_43_7 : Diagram 5 := tableDiagram (by decide) [7, 3, 6, 1, 8, 9, 2, 0, 4, 5] (by decide) (by decide)
theorem cert5_43_7 : MaxTwo d5_43_7 → FiveProperty d5_43_7 := by
  intro h
  have hg : genusRange d5_43_7 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_43_8 : Diagram 5 := tableDiagram (by decide) [7, 3, 6, 1, 9, 8, 2, 0, 5, 4] (by decide) (by decide)
theorem cert5_43_8 : MaxTwo d5_43_8 → FiveProperty d5_43_8 := by
  intro h
  have hg : genusRange d5_43_8 3 := ⟨maskSides5 16, by decide⟩
  have := h 3 hg
  omega
def d5_43_9 : Diagram 5 := tableDiagram (by decide) [7, 3, 8, 1, 5, 4, 9, 0, 2, 6] (by decide) (by decide)
theorem cert5_43_9 : MaxTwo d5_43_9 → FiveProperty d5_43_9 := by
  intro h
  have hg : genusRange d5_43_9 3 := ⟨maskSides5 16, by decide⟩
  have := h 3 hg
  omega
def d5_43_10 : Diagram 5 := tableDiagram (by decide) [7, 3, 8, 1, 6, 9, 4, 0, 2, 5] (by decide) (by decide)
theorem cert5_43_10 : MaxTwo d5_43_10 → FiveProperty d5_43_10 := by
  intro h
  have hg : genusRange d5_43_10 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_43_11 : Diagram 5 := tableDiagram (by decide) [7, 3, 8, 1, 9, 6, 5, 0, 2, 4] (by decide) (by decide)
theorem cert5_43_11 : MaxTwo d5_43_11 → FiveProperty d5_43_11 := by
  intro h
  have hg : genusRange d5_43_11 3 := ⟨maskSides5 32, by decide⟩
  have := h 3 hg
  omega
def d5_43_12 : Diagram 5 := tableDiagram (by decide) [7, 3, 9, 1, 5, 4, 8, 0, 6, 2] (by decide) (by decide)
theorem cert5_43_12 : MaxTwo d5_43_12 → FiveProperty d5_43_12 := by
  intro _
  constructor
  · exact ⟨4, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_43_12) h)
def d5_43_13 : Diagram 5 := tableDiagram (by decide) [7, 3, 9, 1, 6, 8, 4, 0, 5, 2] (by decide) (by decide)
theorem cert5_43_13 : MaxTwo d5_43_13 → FiveProperty d5_43_13 := by
  intro h
  have hg : genusRange d5_43_13 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_43_14 : Diagram 5 := tableDiagram (by decide) [7, 3, 9, 1, 8, 6, 5, 0, 4, 2] (by decide) (by decide)
theorem cert5_43_14 : MaxTwo d5_43_14 → FiveProperty d5_43_14 := by
  intro _
  constructor
  · exact ⟨5, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_43_14) h)
theorem cases5_43 (P : Diagram 5 → Prop)
    (c0 : P d5_43_0)
    (c1 : P d5_43_1)
    (c2 : P d5_43_2)
    (c3 : P d5_43_3)
    (c4 : P d5_43_4)
    (c5 : P d5_43_5)
    (c6 : P d5_43_6)
    (c7 : P d5_43_7)
    (c8 : P d5_43_8)
    (c9 : P d5_43_9)
    (c10 : P d5_43_10)
    (c11 : P d5_43_11)
    (c12 : P d5_43_12)
    (c13 : P d5_43_13)
    (c14 : P d5_43_14)
    (D : Diagram 5) (h0 : D.partner 0 = 7) (h7 : D.partner 7 = 0) (h1 : D.partner 1 = 3) (h3 : D.partner 3 = 1) : P D := by
  have opts : D.partner 2 = 4 ∨ D.partner 2 = 5 ∨ D.partner 2 = 6 ∨ D.partner 2 = 8 ∨ D.partner 2 = 9 := by
    have inv := D.involutive 2
    have nf := D.noFixed 2
    generalize hv : D.partner 2 = v
    fin_cases v <;> simp_all
  rcases opts with h2_4 | h2_5 | h2_6 | h2_8 | h2_9
  · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
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
      have hd : D = d5_43_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_43_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_43_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
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
      have hd : D = d5_43_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_43_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_43_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
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
      have hd : D = d5_43_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_43_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_43_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h8 : D.partner 8 = 2 := by simpa only [h2_8] using D.involutive 2
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
      have hd : D = d5_43_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_43_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_43_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h9 : D.partner 9 = 2 := by simpa only [h2_9] using D.involutive 2
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
      have hd : D = d5_43_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_43_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_43_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_43_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed5_43 (D : Diagram 5) (h0 : D.partner 0 = 7) (h7 : D.partner 7 = 0) (h1 : D.partner 1 = 3) (h3 : D.partner 3 = 1) : MaxTwo D → FiveProperty D :=
  cases5_43 (fun E => MaxTwo E → FiveProperty E) cert5_43_0 cert5_43_1 cert5_43_2 cert5_43_3 cert5_43_4 cert5_43_5 cert5_43_6 cert5_43_7 cert5_43_8 cert5_43_9 cert5_43_10 cert5_43_11 cert5_43_12 cert5_43_13 cert5_43_14 D h0 h7 h1 h3
end Chord.Comb2
