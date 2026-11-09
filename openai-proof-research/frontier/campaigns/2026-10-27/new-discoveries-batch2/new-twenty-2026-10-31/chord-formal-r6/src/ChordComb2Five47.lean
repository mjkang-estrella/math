import ChordComb2Base
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
def d5_47_0 : Diagram 5 := tableDiagram (by decide) [7, 8, 3, 2, 5, 4, 9, 0, 1, 6] (by decide) (by decide)
theorem cert5_47_0 : MaxTwo d5_47_0 → FiveProperty d5_47_0 := by
  intro _
  constructor
  · exact ⟨2, by decide, by decide⟩
  · intro _
    apply Relation.EqvGen.rel
    refine ⟨dihedral5 4 false, ?_, ?_⟩
    · exact Or.inl ⟨4, by decide⟩
    · decide
def d5_47_1 : Diagram 5 := tableDiagram (by decide) [7, 8, 3, 2, 6, 9, 4, 0, 1, 5] (by decide) (by decide)
theorem cert5_47_1 : MaxTwo d5_47_1 → FiveProperty d5_47_1 := by
  intro h
  have hg : genusRange d5_47_1 3 := ⟨maskSides5 4, by decide⟩
  have := h 3 hg
  omega
def d5_47_2 : Diagram 5 := tableDiagram (by decide) [7, 8, 3, 2, 9, 6, 5, 0, 1, 4] (by decide) (by decide)
theorem cert5_47_2 : MaxTwo d5_47_2 → FiveProperty d5_47_2 := by
  intro h
  have hg : genusRange d5_47_2 3 := ⟨maskSides5 36, by decide⟩
  have := h 3 hg
  omega
def d5_47_3 : Diagram 5 := tableDiagram (by decide) [7, 8, 4, 5, 2, 3, 9, 0, 1, 6] (by decide) (by decide)
theorem cert5_47_3 : MaxTwo d5_47_3 → FiveProperty d5_47_3 := by
  intro h
  have hg : genusRange d5_47_3 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_47_4 : Diagram 5 := tableDiagram (by decide) [7, 8, 4, 6, 2, 9, 3, 0, 1, 5] (by decide) (by decide)
theorem cert5_47_4 : MaxTwo d5_47_4 → FiveProperty d5_47_4 := by
  intro h
  have hg : genusRange d5_47_4 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_47_5 : Diagram 5 := tableDiagram (by decide) [7, 8, 4, 9, 2, 6, 5, 0, 1, 3] (by decide) (by decide)
theorem cert5_47_5 : MaxTwo d5_47_5 → FiveProperty d5_47_5 := by
  intro h
  have hg : genusRange d5_47_5 3 := ⟨maskSides5 32, by decide⟩
  have := h 3 hg
  omega
def d5_47_6 : Diagram 5 := tableDiagram (by decide) [7, 8, 5, 4, 3, 2, 9, 0, 1, 6] (by decide) (by decide)
theorem cert5_47_6 : MaxTwo d5_47_6 → FiveProperty d5_47_6 := by
  intro h
  have hg : genusRange d5_47_6 3 := ⟨maskSides5 9, by decide⟩
  have := h 3 hg
  omega
def d5_47_7 : Diagram 5 := tableDiagram (by decide) [7, 8, 5, 6, 9, 2, 3, 0, 1, 4] (by decide) (by decide)
theorem cert5_47_7 : MaxTwo d5_47_7 → FiveProperty d5_47_7 := by
  intro h
  have hg : genusRange d5_47_7 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_47_8 : Diagram 5 := tableDiagram (by decide) [7, 8, 5, 9, 6, 2, 4, 0, 1, 3] (by decide) (by decide)
theorem cert5_47_8 : MaxTwo d5_47_8 → FiveProperty d5_47_8 := by
  intro h
  have hg : genusRange d5_47_8 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_47_9 : Diagram 5 := tableDiagram (by decide) [7, 8, 6, 4, 3, 9, 2, 0, 1, 5] (by decide) (by decide)
theorem cert5_47_9 : MaxTwo d5_47_9 → FiveProperty d5_47_9 := by
  intro h
  have hg : genusRange d5_47_9 3 := ⟨maskSides5 8, by decide⟩
  have := h 3 hg
  omega
def d5_47_10 : Diagram 5 := tableDiagram (by decide) [7, 8, 6, 5, 9, 3, 2, 0, 1, 4] (by decide) (by decide)
theorem cert5_47_10 : MaxTwo d5_47_10 → FiveProperty d5_47_10 := by
  intro h
  have hg : genusRange d5_47_10 3 := ⟨maskSides5 4, by decide⟩
  have := h 3 hg
  omega
def d5_47_11 : Diagram 5 := tableDiagram (by decide) [7, 8, 6, 9, 5, 4, 2, 0, 1, 3] (by decide) (by decide)
theorem cert5_47_11 : MaxTwo d5_47_11 → FiveProperty d5_47_11 := by
  intro h
  have hg : genusRange d5_47_11 3 := ⟨maskSides5 16, by decide⟩
  have := h 3 hg
  omega
def d5_47_12 : Diagram 5 := tableDiagram (by decide) [7, 8, 9, 4, 3, 6, 5, 0, 1, 2] (by decide) (by decide)
theorem cert5_47_12 : MaxTwo d5_47_12 → FiveProperty d5_47_12 := by
  intro _
  constructor
  · exact ⟨3, by decide, by decide⟩
  · intro _
    apply Relation.EqvGen.rel
    refine ⟨dihedral5 3 false, ?_, ?_⟩
    · exact Or.inl ⟨3, by decide⟩
    · decide
def d5_47_13 : Diagram 5 := tableDiagram (by decide) [7, 8, 9, 5, 6, 3, 4, 0, 1, 2] (by decide) (by decide)
theorem cert5_47_13 : MaxTwo d5_47_13 → FiveProperty d5_47_13 := by
  intro h
  have hg : genusRange d5_47_13 3 := ⟨maskSides5 1, by decide⟩
  have := h 3 hg
  omega
def d5_47_14 : Diagram 5 := tableDiagram (by decide) [7, 8, 9, 6, 5, 4, 3, 0, 1, 2] (by decide) (by decide)
theorem cert5_47_14 : MaxTwo d5_47_14 → FiveProperty d5_47_14 := by
  intro h
  have hg : genusRange d5_47_14 3 := ⟨maskSides5 17, by decide⟩
  have := h 3 hg
  omega
theorem cases5_47 (P : Diagram 5 → Prop)
    (c0 : P d5_47_0)
    (c1 : P d5_47_1)
    (c2 : P d5_47_2)
    (c3 : P d5_47_3)
    (c4 : P d5_47_4)
    (c5 : P d5_47_5)
    (c6 : P d5_47_6)
    (c7 : P d5_47_7)
    (c8 : P d5_47_8)
    (c9 : P d5_47_9)
    (c10 : P d5_47_10)
    (c11 : P d5_47_11)
    (c12 : P d5_47_12)
    (c13 : P d5_47_13)
    (c14 : P d5_47_14)
    (D : Diagram 5) (h0 : D.partner 0 = 7) (h7 : D.partner 7 = 0) (h1 : D.partner 1 = 8) (h8 : D.partner 8 = 1) : P D := by
  have opts : D.partner 2 = 3 ∨ D.partner 2 = 4 ∨ D.partner 2 = 5 ∨ D.partner 2 = 6 ∨ D.partner 2 = 9 := by
    have inv := D.involutive 2
    have nf := D.noFixed 2
    generalize hv : D.partner 2 = v
    fin_cases v <;> simp_all
  rcases opts with h2_3 | h2_4 | h2_5 | h2_6 | h2_9
  · have h3 : D.partner 3 = 2 := by simpa only [h2_3] using D.involutive 2
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
      have hd : D = d5_47_0 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_0, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c0
    · have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_47_1 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_1, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c1
    · have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_47_2 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_2, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c2
  · have h4 : D.partner 4 = 2 := by simpa only [h2_4] using D.involutive 2
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
      have hd : D = d5_47_3 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_3, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c3
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_47_4 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_4, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c4
    · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_47_5 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_5, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c5
  · have h5 : D.partner 5 = 2 := by simpa only [h2_5] using D.involutive 2
    have opts : D.partner 3 = 4 ∨ D.partner 3 = 6 ∨ D.partner 3 = 9 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_4 | h3_6 | h3_9
    · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have opts : D.partner 6 = 9 := by
        have inv := D.involutive 6
        have nf := D.noFixed 6
        generalize hv : D.partner 6 = v
        fin_cases v <;> simp_all
      have h6_9 := opts
      have h9 : D.partner 9 = 6 := by simpa only [h6_9] using D.involutive 6
      have hd : D = d5_47_6 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_6, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c6
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 4 = 9 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_9 := opts
      have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have hd : D = d5_47_7 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_7, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c7
    · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
      have opts : D.partner 4 = 6 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_6 := opts
      have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have hd : D = d5_47_8 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_8, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c8
  · have h6 : D.partner 6 = 2 := by simpa only [h2_6] using D.involutive 2
    have opts : D.partner 3 = 4 ∨ D.partner 3 = 5 ∨ D.partner 3 = 9 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_4 | h3_5 | h3_9
    · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have opts : D.partner 5 = 9 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_9 := opts
      have h9 : D.partner 9 = 5 := by simpa only [h5_9] using D.involutive 5
      have hd : D = d5_47_9 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_9, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c9
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 4 = 9 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_9 := opts
      have h9 : D.partner 9 = 4 := by simpa only [h4_9] using D.involutive 4
      have hd : D = d5_47_10 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_10, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c10
    · have h9 : D.partner 9 = 3 := by simpa only [h3_9] using D.involutive 3
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d5_47_11 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_11, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c11
  · have h9 : D.partner 9 = 2 := by simpa only [h2_9] using D.involutive 2
    have opts : D.partner 3 = 4 ∨ D.partner 3 = 5 ∨ D.partner 3 = 6 := by
      have inv := D.involutive 3
      have nf := D.noFixed 3
      generalize hv : D.partner 3 = v
      fin_cases v <;> simp_all
    rcases opts with h3_4 | h3_5 | h3_6
    · have h4 : D.partner 4 = 3 := by simpa only [h3_4] using D.involutive 3
      have opts : D.partner 5 = 6 := by
        have inv := D.involutive 5
        have nf := D.noFixed 5
        generalize hv : D.partner 5 = v
        fin_cases v <;> simp_all
      have h5_6 := opts
      have h6 : D.partner 6 = 5 := by simpa only [h5_6] using D.involutive 5
      have hd : D = d5_47_12 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_12, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c12
    · have h5 : D.partner 5 = 3 := by simpa only [h3_5] using D.involutive 3
      have opts : D.partner 4 = 6 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_6 := opts
      have h6 : D.partner 6 = 4 := by simpa only [h4_6] using D.involutive 4
      have hd : D = d5_47_13 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_13, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c13
    · have h6 : D.partner 6 = 3 := by simpa only [h3_6] using D.involutive 3
      have opts : D.partner 4 = 5 := by
        have inv := D.involutive 4
        have nf := D.noFixed 4
        generalize hv : D.partner 4 = v
        fin_cases v <;> simp_all
      have h4_5 := opts
      have h5 : D.partner 5 = 4 := by simpa only [h4_5] using D.involutive 4
      have hd : D = d5_47_14 := by
        apply diagram_ext
        funext i
        fin_cases i <;> simpa only [d5_47_14, tableDiagram] using (by assumption : D.partner _ = _)
      exact hd ▸ c14
theorem closed5_47 (D : Diagram 5) (h0 : D.partner 0 = 7) (h7 : D.partner 7 = 0) (h1 : D.partner 1 = 8) (h8 : D.partner 8 = 1) : MaxTwo D → FiveProperty D :=
  cases5_47 (fun E => MaxTwo E → FiveProperty E) cert5_47_0 cert5_47_1 cert5_47_2 cert5_47_3 cert5_47_4 cert5_47_5 cert5_47_6 cert5_47_7 cert5_47_8 cert5_47_9 cert5_47_10 cert5_47_11 cert5_47_12 cert5_47_13 cert5_47_14 D h0 h7 h1 h8
end Chord.Comb2
