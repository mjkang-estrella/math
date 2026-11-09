import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d5_20_0 : Diagram 5 := tableDiagram (by decide) [3, 9, 4, 0, 2, 6, 5, 8, 7, 1] (by decide) (by decide)
theorem cert5_20_0 : MaxTwo d5_20_0 → FiveProperty d5_20_0 := by
  intro _
  constructor
  · exact ⟨5, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_20_0) h)
def d5_20_1 : Diagram 5 := tableDiagram (by decide) [3, 9, 4, 0, 2, 7, 8, 5, 6, 1] (by decide) (by decide)
theorem cert5_20_1 : MaxTwo d5_20_1 → FiveProperty d5_20_1 := by
  intro h
  have hg : genusRange d5_20_1 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_20_2 : Diagram 5 := tableDiagram (by decide) [3, 9, 4, 0, 2, 8, 7, 6, 5, 1] (by decide) (by decide)
theorem cert5_20_2 : MaxTwo d5_20_2 → FiveProperty d5_20_2 := by
  intro _
  constructor
  · exact ⟨5, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_20_2) h)
def d5_20_3 : Diagram 5 := tableDiagram (by decide) [3, 9, 5, 0, 6, 2, 4, 8, 7, 1] (by decide) (by decide)
theorem cert5_20_3 : MaxTwo d5_20_3 → FiveProperty d5_20_3 := by
  intro _
  constructor
  · exact ⟨7, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_20_3) h)
def d5_20_4 : Diagram 5 := tableDiagram (by decide) [3, 9, 5, 0, 7, 2, 8, 4, 6, 1] (by decide) (by decide)
theorem cert5_20_4 : MaxTwo d5_20_4 → FiveProperty d5_20_4 := by
  intro h
  have hg : genusRange d5_20_4 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_20_5 : Diagram 5 := tableDiagram (by decide) [3, 9, 5, 0, 8, 2, 7, 6, 4, 1] (by decide) (by decide)
theorem cert5_20_5 : MaxTwo d5_20_5 → FiveProperty d5_20_5 := by
  intro _
  constructor
  · exact ⟨6, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_20_5) h)
def d5_20_6 : Diagram 5 := tableDiagram (by decide) [3, 9, 6, 0, 5, 4, 2, 8, 7, 1] (by decide) (by decide)
theorem cert5_20_6 : MaxTwo d5_20_6 → FiveProperty d5_20_6 := by
  intro _
  constructor
  · exact ⟨4, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_20_6) h)
def d5_20_7 : Diagram 5 := tableDiagram (by decide) [3, 9, 6, 0, 7, 8, 2, 4, 5, 1] (by decide) (by decide)
theorem cert5_20_7 : MaxTwo d5_20_7 → FiveProperty d5_20_7 := by
  intro h
  have hg : genusRange d5_20_7 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_20_8 : Diagram 5 := tableDiagram (by decide) [3, 9, 6, 0, 8, 7, 2, 5, 4, 1] (by decide) (by decide)
theorem cert5_20_8 : MaxTwo d5_20_8 → FiveProperty d5_20_8 := by
  intro h
  have hg : genusRange d5_20_8 3 := ⟨maskSides5 16, by decide⟩
  have := h 3 hg
  omega
def d5_20_9 : Diagram 5 := tableDiagram (by decide) [3, 9, 7, 0, 5, 4, 8, 2, 6, 1] (by decide) (by decide)
theorem cert5_20_9 : MaxTwo d5_20_9 → FiveProperty d5_20_9 := by
  intro _
  constructor
  · exact ⟨4, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_20_9) h)
def d5_20_10 : Diagram 5 := tableDiagram (by decide) [3, 9, 7, 0, 6, 8, 4, 2, 5, 1] (by decide) (by decide)
theorem cert5_20_10 : MaxTwo d5_20_10 → FiveProperty d5_20_10 := by
  intro h
  have hg : genusRange d5_20_10 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_20_11 : Diagram 5 := tableDiagram (by decide) [3, 9, 7, 0, 8, 6, 5, 2, 4, 1] (by decide) (by decide)
theorem cert5_20_11 : MaxTwo d5_20_11 → FiveProperty d5_20_11 := by
  intro _
  constructor
  · exact ⟨5, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_20_11) h)
def d5_20_12 : Diagram 5 := tableDiagram (by decide) [3, 9, 8, 0, 5, 4, 7, 6, 2, 1] (by decide) (by decide)
theorem cert5_20_12 : MaxTwo d5_20_12 → FiveProperty d5_20_12 := by
  intro _
  constructor
  · exact ⟨4, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_20_12) h)
def d5_20_13 : Diagram 5 := tableDiagram (by decide) [3, 9, 8, 0, 6, 7, 4, 5, 2, 1] (by decide) (by decide)
theorem cert5_20_13 : MaxTwo d5_20_13 → FiveProperty d5_20_13 := by
  intro h
  have hg : genusRange d5_20_13 3 := ⟨maskSides5 2, by decide⟩
  have := h 3 hg
  omega
def d5_20_14 : Diagram 5 := tableDiagram (by decide) [3, 9, 8, 0, 7, 6, 5, 4, 2, 1] (by decide) (by decide)
theorem cert5_20_14 : MaxTwo d5_20_14 → FiveProperty d5_20_14 := by
  intro _
  constructor
  · exact ⟨4, by decide, by decide⟩
  · intro h
    exact False.elim ((by decide : ¬HasTriangle d5_20_14) h)
theorem cases5_20 (P : Diagram 5 → Prop)
    (c0 : P d5_20_0)
    (c1 : P d5_20_1)
    (c2 : P d5_20_2)
    (c3 : P d5_20_3)
    (c4 : P d5_20_4)
    (c5 : P d5_20_5)
    (c6 : P d5_20_6)
    (c7 : P d5_20_7)
    (c8 : P d5_20_8)
    (c9 : P d5_20_9)
    (c10 : P d5_20_10)
    (c11 : P d5_20_11)
    (c12 : P d5_20_12)
    (c13 : P d5_20_13)
    (c14 : P d5_20_14)
    (D : Diagram 5) (h0 : D.partner 0 = 3) (h3 : D.partner 3 = 0) (h1 : D.partner 1 = 9) (h9 : D.partner 9 = 1) : P D := by
  have opts : D.partner 2 = 4 ∨ D.partner 2 = 5 ∨ D.partner 2 = 6 ∨ D.partner 2 = 7 ∨ D.partner 2 = 8 := by
    have inv := D.involutive 2
    have nf := D.noFixed 2
    generalize hv : D.partner 2 = v
    fin_cases v <;> simp_all
  rcases opts with h2_4 | h2_5 | h2_6 | h2_7 | h2_8
  · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
    have opts : D.partner 5 = 6 ∨ D.partner 5 = 7 ∨ D.partner 5 = 8 := by
      have inv := D.involutive 5
      have nf := D.noFixed 5
      generalize hv : D.partner 5 = v
      fin_cases v <;> simp_all
    rcases opts with h5_6 | h5_7 | h5_8
    · have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_20_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_20_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d5_20_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
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
      have hd : D = d5_20_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_20_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d5_20_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
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
      have hd : D = d5_20_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_20_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d5_20_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
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
      have hd : D = d5_20_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 8 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_8 := opts
      have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have hd : D = d5_20_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h8 : D.partner 8 = 4 := by simpa only [h4_8] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_20_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h8 : D.partner 8 = 2 := by simpa only [h2_8] using D.involutive 2
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
      have hd : D = d5_20_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 7 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_7 := opts
      have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have hd : D = d5_20_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h7 : D.partner 7 = 4 := by simpa only [h4_7] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_20_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_20_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed5_20 (D : Diagram 5) (h0 : D.partner 0 = 3) (h3 : D.partner 3 = 0) (h1 : D.partner 1 = 9) (h9 : D.partner 9 = 1) : MaxTwo D → FiveProperty D :=
  cases5_20 (fun E => MaxTwo E → FiveProperty E) cert5_20_0 cert5_20_1 cert5_20_2 cert5_20_3 cert5_20_4 cert5_20_5 cert5_20_6 cert5_20_7 cert5_20_8 cert5_20_9 cert5_20_10 cert5_20_11 cert5_20_12 cert5_20_13 cert5_20_14 D h0 h3 h1 h9
end Chord.Comb2
