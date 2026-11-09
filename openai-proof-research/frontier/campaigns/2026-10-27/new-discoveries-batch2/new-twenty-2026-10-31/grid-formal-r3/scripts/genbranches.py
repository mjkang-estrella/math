from pathlib import Path
p=Path(__file__).resolve().parent.parent
corners=[(0,0),(0,2),(2,0),(2,2)]
edges=[(0,1),(1,0),(1,2),(2,1)]
s=''
for i in range(3):
 for j in range(3):
  for k in range(3):
   for l in range(3):
    u,v=(i,j),(k,l)
    if u in corners and v in corners:
     c,d=corners.index(u),corners.index(v)
     s+=f'  · change r ({i},{j}) ({k},{l}) ↔ ((0, codes4 a {c}) : ℕ × ℕ) = (0, codes4 a {d})\n    exact (hc {c} {d}).trans (by simp only [Prod.mk.injEq, true_and])\n'
    elif u in edges and v in edges:
     c,d=edges.index(u),edges.index(v)
     s+=f'  · change r ({i},{j}) ({k},{l}) ↔ ((1, codes4 b {c}) : ℕ × ℕ) = (1, codes4 b {d})\n    exact (he {c} {d}).trans (by simp only [Prod.mk.injEq, true_and])\n'
    elif u==v:
     s+='  · exact iff_of_true (r.refl _) rfl\n'
    else:
     s+=f'  · constructor\n    · intro h\n      exact False.elim ((by decide : ¬ (loc3 ({i},{j})).1 = (loc3 ({k},{l})).1) (hd _ _ h))\n    · intro h\n      change code3 a b ({i},{j}) = code3 a b ({k},{l}) at h\n      exact False.elim ((by decide : ¬ (loc3 ({i},{j})).1.val = (loc3 ({k},{l})).1.val) (congrArg Prod.fst h))\n'
f=p/'src/GridExceptionalPartitions.lean'
f.write_text(f.read_text().split('  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l')[0]+'  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l\n'+s+'end Grid343536\n')
