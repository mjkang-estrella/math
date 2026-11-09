from pathlib import Path
import json
r=Path(__file__).resolve().parent.parent
mods=[]
for n,N in [(27,819),(28,3185)]:
 chunks=[]
 step=128 if n==27 else 32
 starts=list(range(0,N,step)) if n==27 else list(range(0,1984,32))+list(range(1984,N,16))
 for idx,start in enumerate(starts):
  count=min(128 if n==27 else (32 if start<1984 else 16),N-start);m=f'Link{n}_{idx:03d}';chunks.append((m,start,count));mods.append(m)
  (r/'src'/f'{m}.lean').write_text(f'''import TableLinks
import Masks{n}
set_option maxRecDepth 20000
set_option exponentiation.threshold 200000
set_option maxHeartbeats 10000000
namespace Schrijver
theorem {m}_checked : tableLinkCheck vertexMasks{n} maskAt{n} {start} {count} = true := by decide
end Schrijver
''')
 m=f'Table{n}';mods.append(m)
 s=''.join(f'import {c}\n' for c,_,_ in chunks)+'set_option maxRecDepth 20000\nset_option maxHeartbeats 10000000\nnamespace Schrijver\n'
 s+=f'theorem table{n}_size : vertexMasks{n}.size = {N} := by decide\n'
 s+=f'theorem table{n}_links (i : Fin {N}) : maskAt{n} i.val = vertexMasks{n}[i.val]! ∧ (i.val+1 < vertexMasks{n}.size → maskAt{n} i.val < maskAt{n} (i.val+1)) := by\n'
 for j,(c,start,count) in enumerate(chunks):
  if j<len(chunks)-1:
   s+=f'  by_cases h{j} : i.val < {start+count}\n  · exact tableLinkCheck_sound {c}_checked (by omega)\n'
  else:s+=f'  exact tableLinkCheck_sound {c}_checked (by have := i.isLt; omega)\n'
 s+=f'''theorem maskAt{n}_lookup (i : Fin {N}) : maskAt{n} i.val = vertexMasks{n}[i.val]! := (table{n}_links i).1

theorem maskAt{n}_injective : Function.Injective (fun i : Fin {N} => maskAt{n} i.val) := by
  apply (bounded_strictMono maskAt{n} ?_).injective
  intro i hi
  exact (table{n}_links ⟨i, by omega⟩).2 (by rw [table{n}_size]; exact hi)
end Schrijver
'''
 (r/'src'/f'{m}.lean').write_text(s)
 if n==28:
  for name in [c for c,_,_ in chunks]+[m]:
   p=r/'src'/f'{name}.lean';p.write_text(p.read_text().replace('vertexMasks28','(vertexMasks28.toArray)'))
(r/'outputs/table-modules.json').write_text(json.dumps(mods))
