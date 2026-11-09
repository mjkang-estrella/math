from pathlib import Path
for k in range(4):
    p=Path(f'ChordFour{k}.lean');s=p.read_text()
    # expression grows only linearly with the eight arguments, instead of a dependent Pi enumeration.
    args=' '.join(f'b{i}' for i in range(8))
    c='fun i : Fin 8 => '+''.join(f'if i.val={i} then b{i} else ' for i in range(7))+'b7'
    header=f'def side8{k} ({args} : Bool) : Sides 4 := {c}\n'
    header+=f'theorem side8{k}_complete (c : Sides 4) : c = side8{k} '+ ' '.join(f'(c ⟨{i},by decide⟩)' for i in range(8))+' := by\n  funext i\n'
    # Fin.cases peels each coordinate without any arithmetic tactic or imported enumeration.
    header+='  '+ 'cases i using Fin.cases with\n  | zero => rfl\n  | succ i =>\n'
    for j in range(1,7):
        indent='  '+'  '*j
        header+=indent+'cases i using Fin.cases with\n'+indent+'| zero => rfl\n'+indent+'| succ i =>\n'
    header+='  '+'  '*7+'have : i = 0 := Fin.eq_zero i\n'+'  '+'  '*7+'subst i\n'+'  '+'  '*7+'rfl\n'
    start=s.index(f'theorem exception{k}_values')
    end=s.index(f'theorem exception{k}_one')
    proof=f'theorem exception{k}_raw : ∀ {args} : Bool,\n  boundary exception{k} (side8{k} {args}) = 2 ∨ boundary exception{k} (side8{k} {args}) = 4 := by decide\n'
    proof+=f'theorem exception{k}_values (c : Sides 4) : boundary exception{k} c = 2 ∨ boundary exception{k} c = 4 := by\n  rw [side8{k}_complete c]\n  exact exception{k}_raw '+' '.join(f'(c ⟨{i},by decide⟩)' for i in range(8))+'\n'
    s=s[:start]+header+proof+s[end:]
    # Existing existential Pi search also avoid: finite mask search, tiny witness term.
    s=s.replace(f': ∃ c : Sides 4, HasGenus exception{k} c 1 := by decide',f': ∃ c : Sides 4, HasGenus exception{k} c 1 := by\n  obtain ⟨m,hm⟩ := (by decide : ∃ m : Fin 256, HasGenus exception{k} (maskSides 4 m.val) 1)\n  exact ⟨_,hm⟩')
    s=s.replace(f': ∃ c : Sides 4, HasGenus exception{k} c 2 := by decide',f': ∃ c : Sides 4, HasGenus exception{k} c 2 := by\n  obtain ⟨m,hm⟩ := (by decide : ∃ m : Fin 256, HasGenus exception{k} (maskSides 4 m.val) 2)\n  exact ⟨_,hm⟩')
    p.write_text(s)
