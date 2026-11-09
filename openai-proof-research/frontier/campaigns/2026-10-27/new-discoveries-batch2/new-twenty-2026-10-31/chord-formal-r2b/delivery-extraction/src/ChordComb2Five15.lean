import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d5_15_0 : Diagram 5 := tableDiagram (by decide) [3, 4, 5, 0, 1, 2, 7, 6, 9, 8] (by decide) (by decide)
theorem cert5_15_0 : MaxTwo d5_15_0 → FiveProperty d5_15_0 := by
  intro _
  constructor
  · exact ⟨6, by decide, by decide⟩
  · intro _
    apply Relation.EqvGen.rel
    refine ⟨dihedral5 0 false, ?_, ?_⟩
    · exact Or.inl ⟨0, by decide⟩
    · decide
def d5_15_1 : Diagram 5 := tableDiagram (by decide) [3, 4, 5, 0, 1, 2, 8, 9, 6, 7] (by decide) (by decide)
theorem cert5_15_1 : MaxTwo d5_15_1 → FiveProperty d5_15_1 := by
  intro h
  have hg : genusRange d5_15_1 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_15_2 : Diagram 5 := tableDiagram (by decide) [3, 4, 5, 0, 1, 2, 9, 8, 7, 6] (by decide) (by decide)
theorem cert5_15_2 : MaxTwo d5_15_2 → FiveProperty d5_15_2 := by
  intro h
  have hg : genusRange d5_15_2 3 := ⟨maskSides5 129, by decide⟩
  have := h 3 hg
  omega
def d5_15_3 : Diagram 5 := tableDiagram (by decide) [3, 4, 6, 0, 1, 7, 2, 5, 9, 8] (by decide) (by decide)
theorem cert5_15_3 : MaxTwo d5_15_3 → FiveProperty d5_15_3 := by
  intro h
  have hg : genusRange d5_15_3 3 := ⟨maskSides5 256, by decide⟩
  have := h 3 hg
  omega
def d5_15_4 : Diagram 5 := tableDiagram (by decide) [3, 4, 6, 0, 1, 8, 2, 9, 5, 7] (by decide) (by decide)
theorem cert5_15_4 : MaxTwo d5_15_4 → FiveProperty d5_15_4 := by
  intro h
  have hg : genusRange d5_15_4 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_15_5 : Diagram 5 := tableDiagram (by decide) [3, 4, 6, 0, 1, 9, 2, 8, 7, 5] (by decide) (by decide)
theorem cert5_15_5 : MaxTwo d5_15_5 → FiveProperty d5_15_5 := by
  intro h
  have hg : genusRange d5_15_5 3 := ⟨maskSides5 128, by decide⟩
  have := h 3 hg
  omega
def d5_15_6 : Diagram 5 := tableDiagram (by decide) [3, 4, 7, 0, 1, 6, 5, 2, 9, 8] (by decide) (by decide)
theorem cert5_15_6 : MaxTwo d5_15_6 → FiveProperty d5_15_6 := by
  intro h
  have hg : genusRange d5_15_6 3 := ⟨maskSides5 288, by decide⟩
  have := h 3 hg
  omega
def d5_15_7 : Diagram 5 := tableDiagram (by decide) [3, 4, 7, 0, 1, 8, 9, 2, 5, 6] (by decide) (by decide)
theorem cert5_15_7 : MaxTwo d5_15_7 → FiveProperty d5_15_7 := by
  intro h
  have hg : genusRange d5_15_7 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_15_8 : Diagram 5 := tableDiagram (by decide) [3, 4, 7, 0, 1, 9, 8, 2, 6, 5] (by decide) (by decide)
theorem cert5_15_8 : MaxTwo d5_15_8 → FiveProperty d5_15_8 := by
  intro h
  have hg : genusRange d5_15_8 3 := ⟨maskSides5 32, by decide⟩
  have := h 3 hg
  omega
def d5_15_9 : Diagram 5 := tableDiagram (by decide) [3, 4, 8, 0, 1, 6, 5, 9, 2, 7] (by decide) (by decide)
theorem cert5_15_9 : MaxTwo d5_15_9 → FiveProperty d5_15_9 := by
  intro h
  have hg : genusRange d5_15_9 3 := ⟨maskSides5 32, by decide⟩
  have := h 3 hg
  omega
def d5_15_10 : Diagram 5 := tableDiagram (by decide) [3, 4, 8, 0, 1, 7, 9, 5, 2, 6] (by decide) (by decide)
theorem cert5_15_10 : MaxTwo d5_15_10 → FiveProperty d5_15_10 := by
  intro h
  have hg : genusRange d5_15_10 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_15_11 : Diagram 5 := tableDiagram (by decide) [3, 4, 8, 0, 1, 9, 7, 6, 2, 5] (by decide) (by decide)
theorem cert5_15_11 : MaxTwo d5_15_11 → FiveProperty d5_15_11 := by
  intro h
  have hg : genusRange d5_15_11 3 := ⟨maskSides5 64, by decide⟩
  have := h 3 hg
  omega
def d5_15_12 : Diagram 5 := tableDiagram (by decide) [3, 4, 9, 0, 1, 6, 5, 8, 7, 2] (by decide) (by decide)
theorem cert5_15_12 : MaxTwo d5_15_12 → FiveProperty d5_15_12 := by
  intro _
  constructor
  · exact ⟨5, by decide, by decide⟩
  · intro _
    apply Relation.EqvGen.rel
    refine ⟨dihedral5 1 false, ?_, ?_⟩
    · exact Or.inl ⟨1, by decide⟩
    · decide
def d5_15_13 : Diagram 5 := tableDiagram (by decide) [3, 4, 9, 0, 1, 7, 8, 5, 6, 2] (by decide) (by decide)
theorem cert5_15_13 : MaxTwo d5_15_13 → FiveProperty d5_15_13 := by
  intro h
  have hg : genusRange d5_15_13 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_15_14 : Diagram 5 := tableDiagram (by decide) [3, 4, 9, 0, 1, 8, 7, 6, 5, 2] (by decide) (by decide)
theorem cert5_15_14 : MaxTwo d5_15_14 → FiveProperty d5_15_14 := by
  intro h
  have hg : genusRange d5_15_14 3 := ⟨maskSides5 65, by decide⟩
  have := h 3 hg
  omega
theorem cases5_15 (P : Diagram 5 → Prop)
    (c0 : P d5_15_0)
    (c1 : P d5_15_1)
    (c2 : P d5_15_2)
    (c3 : P d5_15_3)
    (c4 : P d5_15_4)
    (c5 : P d5_15_5)
    (c6 : P d5_15_6)
    (c7 : P d5_15_7)
    (c8 : P d5_15_8)
    (c9 : P d5_15_9)
    (c10 : P d5_15_10)
    (c11 : P d5_15_11)
    (c12 : P d5_15_12)
    (c13 : P d5_15_13)
    (c14 : P d5_15_14)
    (D : Diagram 5) (h0 : D.partner 0 = 3) (h3 : D.partner 3 = 0) (h1 : D.partner 1 = 4) (h4 : D.partner 4 = 1) : P D := by
  have opts : D.partner 2 = 5 ∨ D.partner 2 = 6 ∨ D.partner 2 = 7 ∨ D.partner 2 = 8 ∨ D.partner 2 = 9 := by
    have inv := D.involutive 2
    have nf := D.noFixed 2
    generalize hv : D.partner 2 = v
    fin_cases v <;> simp_all
  rcases opts with h2_5 | h2_6 | h2_7 | h2_8 | h2_9
  · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
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
      have hd : D = d5_15_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have opts : D.partner 7 = 9 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_9 := opts
      have h9 : D.partner 9 = 7 := by simpa only [h7_9] using D.involutive 7
      have hd : D = d5_15_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_15_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
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
      have hd : D = d5_15_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have opts : D.partner 7 = 9 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_9 := opts
      have h9 : D.partner 9 = 7 := by simpa only [h7_9] using D.involutive 7
      have hd : D = d5_15_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have opts : D.partner 7 = 8 := by
        have inv := D.involutive 7
        have nf := D.noFixed 7
        generalize hv : D.partner 7 = v
        fin_cases v <;> simp_all
      have h7_8 := opts
      have h8 : D.partner 8 = 7 := by simpa only [h7_8] using D.involutive 7
      have hd : D = d5_15_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h7 : D.partner 7 = 2 := by simpa only [h2_7] using D.involutive 2
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
      have hd : D = d5_15_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_15_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_15_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h8 : D.partner 8 = 2 := by simpa only [h2_8] using D.involutive 2
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
      have hd : D = d5_15_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_15_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d5_15_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h9 : D.partner 9 = 2 := by simpa only [h2_9] using D.involutive 2
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
      have hd : D = d5_15_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h7 : D.partner 7 = 5 := by simpa only [h5_7] using D.involutive 5
      have opts : D.partner 6 = 8 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_8 := opts
      have h8 : D.partner 8 = 6 := by simpa only [h6_8] using D.involutive 6
      have hd : D = d5_15_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h8 : D.partner 8 = 5 := by simpa only [h5_8] using D.involutive 5
      have opts : D.partner 6 = 7 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_7 := opts
      have h7 : D.partner 7 = 6 := by simpa only [h6_7] using D.involutive 6
      have hd : D = d5_15_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_15_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed5_15 (D : Diagram 5) (h0 : D.partner 0 = 3) (h3 : D.partner 3 = 0) (h1 : D.partner 1 = 4) (h4 : D.partner 4 = 1) : MaxTwo D → FiveProperty D :=
  cases5_15 (fun E => MaxTwo E → FiveProperty E) cert5_15_0 cert5_15_1 cert5_15_2 cert5_15_3 cert5_15_4 cert5_15_5 cert5_15_6 cert5_15_7 cert5_15_8 cert5_15_9 cert5_15_10 cert5_15_11 cert5_15_12 cert5_15_13 cert5_15_14 D h0 h3 h1 h4
end Chord.Comb2
