import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d5_12_0 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 4, 3, 6, 5, 9, 1, 7] (by decide) (by decide)
theorem cert5_12_0 : MaxTwo d5_12_0 → FiveProperty d5_12_0 := by
  intro _
  constructor
  · exact ⟨3, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_12_0) h)
def d5_12_1 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 4, 3, 7, 9, 5, 1, 6] (by decide) (by decide)
theorem cert5_12_1 : MaxTwo d5_12_1 → FiveProperty d5_12_1 := by
  intro _
  constructor
  · exact ⟨3, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_12_1) h)
def d5_12_2 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 4, 3, 9, 7, 6, 1, 5] (by decide) (by decide)
theorem cert5_12_2 : MaxTwo d5_12_2 → FiveProperty d5_12_2 := by
  intro _
  constructor
  · exact ⟨3, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_12_2) h)
def d5_12_3 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 5, 6, 3, 4, 9, 1, 7] (by decide) (by decide)
theorem cert5_12_3 : MaxTwo d5_12_3 → FiveProperty d5_12_3 := by
  intro h
  have hg : genusRange d5_12_3 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_12_4 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 5, 7, 3, 9, 4, 1, 6] (by decide) (by decide)
theorem cert5_12_4 : MaxTwo d5_12_4 → FiveProperty d5_12_4 := by
  intro h
  have hg : genusRange d5_12_4 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_12_5 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 5, 9, 3, 7, 6, 1, 4] (by decide) (by decide)
theorem cert5_12_5 : MaxTwo d5_12_5 → FiveProperty d5_12_5 := by
  intro _
  constructor
  · exact ⟨6, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_12_5) h)
def d5_12_6 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 6, 5, 4, 3, 9, 1, 7] (by decide) (by decide)
theorem cert5_12_6 : MaxTwo d5_12_6 → FiveProperty d5_12_6 := by
  intro _
  constructor
  · exact ⟨3, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_12_6) h)
def d5_12_7 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 6, 7, 9, 3, 4, 1, 5] (by decide) (by decide)
theorem cert5_12_7 : MaxTwo d5_12_7 → FiveProperty d5_12_7 := by
  intro h
  have hg : genusRange d5_12_7 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_12_8 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 6, 9, 7, 3, 5, 1, 4] (by decide) (by decide)
theorem cert5_12_8 : MaxTwo d5_12_8 → FiveProperty d5_12_8 := by
  intro h
  have hg : genusRange d5_12_8 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_12_9 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 7, 5, 4, 9, 3, 1, 6] (by decide) (by decide)
theorem cert5_12_9 : MaxTwo d5_12_9 → FiveProperty d5_12_9 := by
  intro _
  constructor
  · exact ⟨4, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_12_9) h)
def d5_12_10 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 7, 6, 9, 4, 3, 1, 5] (by decide) (by decide)
theorem cert5_12_10 : MaxTwo d5_12_10 → FiveProperty d5_12_10 := by
  intro h
  have hg : genusRange d5_12_10 3 := ⟨maskSides5 8, by decide⟩
  have := h 3 hg
  omega
def d5_12_11 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 7, 9, 6, 5, 3, 1, 4] (by decide) (by decide)
theorem cert5_12_11 : MaxTwo d5_12_11 → FiveProperty d5_12_11 := by
  intro _
  constructor
  · exact ⟨5, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_12_11) h)
def d5_12_12 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 9, 5, 4, 7, 6, 1, 3] (by decide) (by decide)
theorem cert5_12_12 : MaxTwo d5_12_12 → FiveProperty d5_12_12 := by
  intro _
  constructor
  · exact ⟨4, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_12_12) h)
def d5_12_13 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 9, 6, 7, 4, 5, 1, 3] (by decide) (by decide)
theorem cert5_12_13 : MaxTwo d5_12_13 → FiveProperty d5_12_13 := by
  intro h
  have hg : genusRange d5_12_13 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_12_14 : Diagram 5 := tableDiagram (by decide) [2, 8, 0, 9, 7, 6, 5, 4, 1, 3] (by decide) (by decide)
theorem cert5_12_14 : MaxTwo d5_12_14 → FiveProperty d5_12_14 := by
  intro _
  constructor
  · exact ⟨4, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_12_14) h)
theorem cases5_12 (P : Diagram 5 → Prop)
    (c0 : P d5_12_0)
    (c1 : P d5_12_1)
    (c2 : P d5_12_2)
    (c3 : P d5_12_3)
    (c4 : P d5_12_4)
    (c5 : P d5_12_5)
    (c6 : P d5_12_6)
    (c7 : P d5_12_7)
    (c8 : P d5_12_8)
    (c9 : P d5_12_9)
    (c10 : P d5_12_10)
    (c11 : P d5_12_11)
    (c12 : P d5_12_12)
    (c13 : P d5_12_13)
    (c14 : P d5_12_14)
    (D : Diagram 5) (h0 : D.partner 0 = 2) (h2 : D.partner 2 = 0) (h1 : D.partner 1 = 8) (h8 : D.partner 8 = 1) : P D := by
  have opts : D.partner 3 = 4 ∨ D.partner 3 = 5 ∨ D.partner 3 = 6 ∨ D.partner 3 = 7 ∨ D.partner 3 = 9 := by
    have inv := D.involutive 3
    have nf := D.noFixed 3
    generalize hv : D.partner 3 = v
    fin_cases v <;> simp_all
  rcases opts with h3_4 | h3_5 | h3_6 | h3_7 | h3_9
  · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
    have opts : D.partner 5 = 6 ∨ D.partner 5 = 7 ∨ D.partner 5 = 9 := by
      have inv := D.involutive 5
      have nf := D.noFixed 5
      generalize hv : D.partner 5 = v
      fin_cases v <;> simp_all
    rcases opts with h5_6 | h5_7 | h5_9
    · have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have opts : D.partner 7 = 9 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_9 := opts
      have h9 : D.partner 9 = 7 := by simpa only [h7_9] using D.involutive 7
      have hd : D = d5_12_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_12_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d5_12_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
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
      have hd : D = d5_12_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_12_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d5_12_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
    have opts : D.partner 4 = 5 ∨ D.partner 4 = 7 ∨ D.partner 4 = 9 := by
      have inv := D.involutive 4
      have nf := D.noFixed 4
      generalize hv : D.partner 4 = v
      fin_cases v <;> simp_all
    rcases opts with h4_5 | h4_7 | h4_9
    · have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have opts : D.partner 7 = 9 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_9 := opts
      have h9 : D.partner 9 = 7 := by simpa only [h7_9] using D.involutive 7
      have hd : D = d5_12_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_12_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d5_12_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h7 : D.partner 7 = 3 := by simpa only [h3_7] using D.involutive 3
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
      have hd : D = d5_12_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_12_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_12_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
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
      have hd : D = d5_12_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d5_12_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_12_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_12_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed5_12 (D : Diagram 5) (h0 : D.partner 0 = 2) (h2 : D.partner 2 = 0) (h1 : D.partner 1 = 8) (h8 : D.partner 8 = 1) : MaxTwo D → FiveProperty D :=
  cases5_12 (fun E => MaxTwo E → FiveProperty E) cert5_12_0 cert5_12_1 cert5_12_2 cert5_12_3 cert5_12_4 cert5_12_5 cert5_12_6 cert5_12_7 cert5_12_8 cert5_12_9 cert5_12_10 cert5_12_11 cert5_12_12 cert5_12_13 cert5_12_14 D h0 h2 h1 h8
end Chord.Comb2
