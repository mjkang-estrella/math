from generate_cases import *
ns='F840';p=L/'formal/F840Case.lean';s=p.read_text();imports=s[:s.index('set_option')];pre=s[s.index('set_option'):s.index('def pairs')];pairs=s[s.index('def pairs'):s.index('theorem coverage')];checks=s[s.index('theorem checks'):s.index('theorem case_')];case=s[s.index('theorem case_'):s.rindex('end F840')]
# shared list only, avoid toFinset deduplication in executable coverage checks
base=imports+pre+pairs+'end F840\n'
for d in ['dev','formal']:(L/d/'F840List.lean').write_text(base)
free=sorted([(x,y) for x in range(-10,12) for y in range(-10,12) if 0<=x+y<=8 and 0<=x-y<=4]);forced={(1,0),(2,-1),(2,1),(3,0),(3,2),(4,1),(4,3),(5,2)};free=[p for p in free if p not in forced]
mods=[]
for i in reversed(range(len(free))):
 mod=f'F840Cover{i}';mods.append(mod);suffix=fs(free[i+1:]);whole=fs(free[i:]);pt=str(free[i]).replace(' ','')
 body=f'theorem head{i} : ∀ E ∈ ({suffix} : Finset GridPoint).powersetCard 2, insert {pt} E ∈ pairs.map Prod.fst := by decide\n'
 body+=f'theorem cover{i} : ∀ E ∈ ({whole} : Finset GridPoint).powersetCard 3, E ∈ pairs.map Prod.fst := by\n  intro E hE\n'
 body+=f'  have heq : ({whole} : Finset GridPoint) = insert {pt} {suffix} := by decide\n  rw [heq, show 3 = 2+1 from rfl, Finset.powersetCard_succ_insert (by decide)] at hE\n  rcases Finset.mem_union.mp hE with h | h\n'
 if i==len(free)-1:body+='  · have hf : (∅ : Finset GridPoint).powersetCard 3 = ∅ := by decide\n    rw [hf] at h\n    exact False.elim (Finset.notMem_empty _ h)\n'
 else:body+=f'  · exact cover{i+1} E h\n'
 body+=f'  · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp h\n    exact head{i} T hT\n'
 out='import '+('F840List' if i==len(free)-1 else f'F840Cover{i+1}')+'\n'+pre+body+'end F840\n'
 for d in ['dev','formal']:(L/d/(mod+'.lean')).write_text(out)
coverage='theorem coverage : ∀ E ∈ free.powersetCard 3, E ∈ pairs.map Prod.fst := cover0\n'
case=case.replace('List.mem_toFinset.mp (coverage he)','coverage _ he')
out='import F840Cover0\n'+pre+coverage+checks+case+'end F840\n'
for d in ['dev','formal']:(L/d/'F840Case.lean').write_text(out)
(L/'forced-coverage-plan.txt').write_text('\n'.join(['F840List']+mods+['F840Case'])+'\n')
