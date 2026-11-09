import pathlib
D=pathlib.Path(__file__).resolve().parents[1]
for chunk in range(8):
 s='import Certificate\nnamespace R162\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
 for i in range(11*chunk,11*(chunk+1)):
  s+=f'''theorem row_{i} : ∀ j : Fin 88,
 (treeGraph (nanostar 4)).Adj ({i} : Fin 88) j ↔
 ({i} : Fin 88) ≠ j ∧ (next ({i} : Fin 88) = j ∨ next j = ({i} : Fin 88)) := by
 change ∀ j : Fin 88,
   (({i} : Fin 88) ≠ j ∧ (({i},j.val) ∈ edges (nanostar 4) ∨ (j.val,{i}) ∈ edges (nanostar 4))) ↔
   ({i} : Fin 88) ≠ j ∧ (next ({i} : Fin 88) = j ∨ next j = ({i} : Fin 88))
 decide
'''
 s+='end R162\n';(D/f'lean/EdgeRows{chunk}.lean').write_text(s)
p=D/'lean/Endpoint.lean';s=p.read_text();a=s.index(' := by\n change ∀ i j : Fin 88,',s.index('theorem edge_certificate'));b=s.index('\ntheorem realizable_four',a)
s=s[:a]+''' := by
 intro i
 fin_cases i
'''+''.join(f' · exact row_{i}\n' for i in range(88))+s[b:]
s=s.replace('import Certificate','\n'.join(f'import EdgeRows{c}' for c in range(8)))
p.write_text(s)
