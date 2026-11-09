from pathlib import Path
import json,sys
sys.set_int_max_str_digits(0)
r=Path(__file__).resolve().parent.parent
arr=lambda xs:'#['+','.join(map(str,xs))+']'
pack=lambda xs,w:sum(x<<(w*i) for i,x in enumerate(xs))
mods=[]
for n in (27,28):
 d=json.loads((r/f'outputs/certificate-{n}.json').read_text());N=len(d['vertices'])
 if n==27:
  name=f'Masks{n}';mods.append(name)
  (r/f'src/{name}.lean').write_text('import IndexedCertificates\nset_option autoImplicit false\nset_option maxRecDepth 20000\nset_option maxHeartbeats 10000000\nnamespace Schrijver\ndef vertexMasks27 : Array Nat := '+arr(d['vertices'])+'\ntheorem vertexMasks27_valid : (vertexMasks27.toList.all (validMask 27 12)) = true := by decide\n'+f'def maskAt27 : Nat → Nat := packedGet 27 {pack(d["vertices"],27)}\nend Schrijver\n')
 else:
  chunks=[]
  for j,lo in enumerate(range(0,N,128)):
   name=f'Valid28_{j:03}';mods.append(name);chunks.append(name)
   (r/f'src/{name}.lean').write_text('import Checkers\nset_option autoImplicit false\nset_option maxRecDepth 20000\nset_option maxHeartbeats 10000000\nnamespace Schrijver\ndef '+name+' : List Nat := ['+','.join(map(str,d['vertices'][lo:lo+128]))+']\ntheorem '+name+'_checked : ('+name+'.all (validMask 28 12)) = true := by decide\nend Schrijver\n')
  name='Masks28';mods.append(name)
  imports='import IndexedCertificates\n'+''.join('import '+x+'\n' for x in chunks)
  text=imports+'set_option autoImplicit false\nnamespace Schrijver\ndef vertexMasks28 : List Nat := '+' ++ '.join(chunks)+'\n'
  text+='theorem vertexMasks28_valid : vertexMasks28.all (validMask 28 12) = true := by\n  simp only [vertexMasks28, List.all_append, '+', '.join(x+'_checked' for x in chunks)+', Bool.and_self]\n'
  text+=f'def maskAt28 : Nat → Nat := packedGet 28 {pack(d["vertices"],28)}\nend Schrijver\n'
  (r/'src/Masks28.lean').write_text(text)
 trees=d['trees'] if n==28 else [next(t for t in d['trees'] if t['source']==d['pair'][0])]
 for j,t in enumerate(trees):
  name=f'Tree{n}_{j:03}';mods.append(name)
  s=f'import Masks{n}\nset_option autoImplicit false\nset_option exponentiation.threshold 200000\nset_option maxRecDepth 20000\nset_option maxHeartbeats 10000000\nnamespace Schrijver\nnamespace {name}\n'
  s+='def parents : Nat → Nat := packedGet 12 '+str(pack(t['parents'],12))+'\ndef depths : Nat → Nat := packedGet 4 '+str(pack(t['labels'],4))+'\n'
  s+=f'def root : Fin {N} := ⟨{t["source"]}, by decide⟩\n'
  s+=f'theorem checked : treeCheck {N} maskAt{n} parents depths root {max(t["labels"])} = true := by decide\n'
  s+=f'theorem sound : (indexedGraph {N} maskAt{n}).Connected ∧ ∀ v, ∃ p : (indexedGraph {N} maskAt{n}).Walk v root, p.length ≤ {max(t["labels"])} := treeCheck_sound _ _ _ _ _ _ checked\n'
  s+=f'end {name}\nend Schrijver\n';(r/f'src/{name}.lean').write_text(s)
 (r/'outputs/kernel-modules.json').write_text(json.dumps(mods,indent=2)+'\n')
