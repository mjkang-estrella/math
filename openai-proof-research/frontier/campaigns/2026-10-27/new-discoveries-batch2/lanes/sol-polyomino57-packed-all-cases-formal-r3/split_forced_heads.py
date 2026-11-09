from generate_cases import *
free=sorted([(x,y) for x in range(-10,12) for y in range(-10,12) if 0<=x+y<=8 and 0<=x-y<=4]);forced={(1,0),(2,-1),(2,1),(3,0),(3,2),(4,1),(4,3),(5,2)};free=[p for p in free if p not in forced]
pre=(L/'formal/F840List.lean').read_text();pre=pre[pre.index('set_option'):pre.index('def pairs')];plan=[]
for i in range(6):
 p=str(free[i]).replace(' ','')
 for j in reversed(range(i+1,len(free))):
  q=str(free[j]).replace(' ','');suffix=fs(free[j+1:]);whole=fs(free[j:]);mod=f'F840Head{i}_{j}';prev='F840List' if j+1==len(free) else f'F840Head{i}_{j+1}'
  body=f'theorem pair{i}_{j} : ∀ T ∈ ({suffix} : Finset GridPoint).powersetCard 1, insert {p} (insert {q} T) ∈ pairs.map Prod.fst := by decide\n'
  body+=f'theorem head{i}_{j} : ∀ E ∈ ({whole} : Finset GridPoint).powersetCard 2, insert {p} E ∈ pairs.map Prod.fst := by\n  intro E hE\n  have heq : ({whole} : Finset GridPoint) = insert {q} {suffix} := by decide\n  rw [heq, show 2 = 1+1 from rfl, Finset.powersetCard_succ_insert (by decide)] at hE\n  rcases Finset.mem_union.mp hE with h | h\n'
  if j+1==len(free):body+='  · have hf : (∅ : Finset GridPoint).powersetCard 2 = ∅ := by decide\n    rw [hf] at h\n    exact False.elim (Finset.notMem_empty _ h)\n'
  else:body+=f'  · exact head{i}_{j+1} E h\n'
  body+=f'  · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp h\n    exact pair{i}_{j} T hT\n'
  for d in ['dev','formal']:(L/d/(mod+'.lean')).write_text('import '+prev+'\n'+pre+body+'end F840\n')
  plan.append(mod)
 # Replace head_i decision with structural proof from new helper.
 for d in ['dev','formal']:
  f=L/d/f'F840Cover{i}.lean';s=f.read_text();pos=s.index(' := by decide',s.index(f'theorem head{i}'));s=s[:pos]+f' := head{i}_{i+1}'+s[pos+len(' := by decide'):];s='import '+f'F840Head{i}_{i+1}\n'+s;f.write_text(s)
# topological then covers 5..0 and case
plan += [f'F840Cover{i}' for i in reversed(range(6))]+['F840Case']
(L/'forced-head-plan.txt').write_text('\n'.join(plan)+'\n')
