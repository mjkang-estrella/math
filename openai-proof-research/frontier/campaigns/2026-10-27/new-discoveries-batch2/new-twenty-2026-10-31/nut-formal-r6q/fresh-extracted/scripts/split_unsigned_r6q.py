from pathlib import Path
import json,re,collections
r=Path(__file__).resolve().parents[1];rs=json.loads((r/'new-certificates.json').read_text());ss=json.loads((r/'new-supports.json').read_text())
for sp in ss:
 f=r/'formal'/f'FiniteSupport{sp["index"]:03}.lean';s=f.read_text();s=re.sub(r'run_cmd do IO.eprintln .*\n','',s);s=s.replace('set_option maxRecDepth 4096','set_option maxRecDepth 4096\nset_option linter.unusedSimpArgs false')
 groups=collections.OrderedDict()
 for n in sp['ids']:
  a=rs[n]['matrix'];key=tuple(abs(x) for row in a for x in row);groups.setdefault(key,[]).append(n)
 lines=[]
 for k,key in enumerate(groups):
  doubles=[]
  for i in range(8):
   for j in range(i+1,8):
    if key[8*i+j]==2:doubles.append(tuple(sorted((sp['order'][i],sp['order'][j]))))
  doubles=sorted(doubles);ds='{'+', '.join(f'({i},{j})' for i,j in doubles)+'}' if doubles else '∅'
  lines += [f'def D{k} : Finset (Fin 8 × Fin 8) := {ds}']
 lines += [f'theorem doubled_enumeration : ((supportEdges {sp["code"]}).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum {sp["code"]} D i ∧ offSum {sp["code"]} D i ≤ 3) = {{{", ".join("D"+str(k) for k in range(len(groups)))}}} := by','  decide +kernel']
 for k in range(len(groups)):
  lines += [f'theorem augmentation{k} : augmentation {sp["code"]} D{k} = U{k} := by','  decide +kernel']
 lines += [f'theorem unsigned_enumeration : unsignedPatterns {sp["code"]} = {{{", ".join("U"+str(k) for k in range(len(groups)))}}} := by','  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, '+', '.join(f'augmentation{k}' for k in range(len(groups)))+']']
 s=re.sub(r'theorem unsigned_enumeration :.*?\n  decide \+kernel\n','\n'.join(lines)+'\n',s,flags=re.S);f.write_text(s)
print('Doubled-edge set decomposition generated')
