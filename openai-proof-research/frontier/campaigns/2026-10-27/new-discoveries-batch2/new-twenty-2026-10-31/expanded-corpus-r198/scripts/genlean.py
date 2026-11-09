import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];z=json.loads((D/'outputs/submod-dual-compressed.json').read_text());coords=[tuple(s) for s in z['coords']];idx={s:i for i,s in enumerate(coords)};perms=list(itertools.permutations(range(5)))
def act(x,p):return sum(1<<idx[tuple(sorted(p[a] for a in s))] for j,s in enumerate(coords) if x>>j&1)
points=sorted({x for a in z['support'] for x in ([a['point']] if a['kind']!='submodular' else [x for x,c in a['terms']])});canon={x:min(act(x,p) for p in perms) for x in points}
s='import Separator\nimport Mathlib.Data.Fin.VecNotation\nnamespace Separation\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\ndef coords : Fin 15 → Finset (Fin 5) := !['+', '.join('{'+','.join(map(str,a))+'}' for a in coords)+']\ndef decode (m : ℕ) : Point 5 := insert ∅ ((Finset.univ.filter (fun j : Fin 15 => m.testBit j.val)).image coords)\n'
for x in points:
 if canon[x]==x:continue
 p=next(p for p in perms if act(x,p)==canon[x]);perm='Equiv.ofBijective (fun i : Fin 5 => !['+','.join(map(str,p))+'] i) (by decide)'
 s+=f'lemma norm{x} (f : Point 5 → ℤ) : avg f (decode {x}) = avg f (decode {canon[x]}) := by\n let t : Equiv.Perm (Fin 5) := {perm}\n have h : rename t (decode {x}) = decode {canon[x]} := by decide\n rw [← h, avg_rename]\n'
s+='theorem no_separator_5_2 : ¬ ∃ f, Separator 5 2 f := by\n rintro ⟨f,hf⟩\n'
normal=[f'norm{x} f' for x in points if canon[x]!=x]
for k,a in enumerate(z['support']):
 if a['kind']=='submodular':
  (meet,_),(join,_),(x,_),(y,_)=a['terms']
  s+=f' have h{k} := avg_submod f hf (decode {x}) (decode {y}) (by decide) (by decide)\n'
  s+=f' have h{k}a : decode {x} ∪ decode {y} = decode {join} := by decide\n have h{k}b : decode {x} ∩ decode {y} = decode {meet} := by decide\n rw [h{k}a,h{k}b] at h{k}\n'
 else:
  x=a['point']
  if a['kind']=='bad':s+=f' have h{k} := avg_bad f hf (decode {x}) (by decide) (by decide)\n'
  else:
   raw=next(t for t in range(32) if sum((all(t>>a&1 for a in c))<<j for j,c in enumerate(coords))==x)
   X='{'+','.join(str(a) for a in range(5) if raw>>a&1)+'}'
   s+=f' have h{k} := avg_good f hf ({X} : Finset (Fin 5))\n have h{k}a : phi 2 ({X} : Finset (Fin 5)) = decode {x} := by decide\n rw [h{k}a] at h{k}\n'
 s+=' simp only ['+', '.join(normal)+f'] at h{k}\n'
s+=' have hc : (Fintype.card (Equiv.Perm (Fin 5)) : ℤ) = 120 := by decide\n';s+=' rw [hc] at h10 h11\n linarith only ['+', '.join('h'+str(k) for k in range(13))+']\ntheorem source_existence_refuted : ¬ SeparationExistence := by\n intro h\n exact no_separator_5_2 (h 5 2 (by decide))\n#print axioms source_existence_refuted\nend Separation\n'
(D/'lean/Certificate.lean').write_text(s)
