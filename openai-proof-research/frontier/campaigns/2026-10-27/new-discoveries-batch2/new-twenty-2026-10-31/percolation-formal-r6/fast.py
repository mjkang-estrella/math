from pathlib import Path
r=Path(__file__).resolve().parent
p=r/'packet/src/MaskRUP.lean'
s=p.read_text().replace('abbrev Hint := Mask × (Nat × Bool)','abbrev Hint := Mask × Option (Nat × Bool)')
a=s.index('      if cover h.1 fs then true');b=s.index('\ntheorem bit_insert',a)
s=s[:a]+'''      match h.2 with
      | none => cover h.1 fs
      | some (n,b) => cover h.1 (insert fs n b) && prev (insert fs n (!b))) hs f
''' + s[b:]
a=s.index('    by_cases hcov');b=s.index('\ntheorem check_sound (',a)
s=s[:a]+'''    cases hu : h.2 with
    | none => exact conflict v h.1 f hf hc (by simpa [check, hu] using he)
    | some z =>
      have hhcheck : cover h.1 (insert f z.1 z.2) = true ∧
          check (insert f z.1 (!z.2)) hs = true := by simpa [check, hu] using he
      apply ih (insert f z.1 (!z.2))
      · exact insert_false v f z.1 (!z.2) hf (force v h.1 f z.1 z.2 hf hc hhcheck.1)
      · intro d hd; exact hh d (by simp [hd])
      · exact hhcheck.2
''' + s[b:]
p.write_text(s)
p=r/'pilot.py';s=p.read_text().replace("if not rem: u=1","if not rem: u=None").replace("hh.append(f'({mask(db[hid])},({abs(u)-1},{str(u<0).lower()}))')", "hh.append(f'({mask(db[hid])},'+('none)' if u is None else f'some ({abs(u)-1},{str(u<0).lower()}))'))")
p.write_text(s)
