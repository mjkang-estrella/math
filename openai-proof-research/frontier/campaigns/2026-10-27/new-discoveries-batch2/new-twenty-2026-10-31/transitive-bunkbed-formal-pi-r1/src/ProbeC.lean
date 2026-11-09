import BunkbedBase
set_option linter.unusedVariables false
variable (n : Nat)
-- exact composite, variable n, obtain-style:
example (t : HToken n) :
    (fun p : {q : Fin n × Fin n // (q.1 : Nat) < (q.2 : Nat)} × Bool =>
      ⟨p.1.1.1, p.1.1.2, p.1.2, p.2⟩)
      ((fun t : HToken n => (⟨(t.fst, t.snd), t.hlt⟩, t.layer)) t) = t := by
  obtain ⟨i, j, h, l⟩ := t
  simp
-- ext-style, no cases on the nested subtype:
example (p : {q : Fin n × Fin n // (q.1 : Nat) < (q.2 : Nat)} × Bool) :
    (fun t : HToken n => (⟨(t.fst, t.snd), t.hlt⟩, t.layer))
      (⟨p.1.1.1, p.1.1.2, p.1.2, p.2⟩) = p := by
  obtain ⟨q, l⟩ := p
  have hq : q = ⟨(q.1.1, q.1.2), q.2⟩ := Subtype.ext rfl
  rw [hq]
  rfl
