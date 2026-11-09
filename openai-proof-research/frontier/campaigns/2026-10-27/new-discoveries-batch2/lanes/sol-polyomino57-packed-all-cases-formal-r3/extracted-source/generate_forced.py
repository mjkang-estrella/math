from generate_cases import *
from itertools import combinations
for a,b,e in [(7,4,0),(8,3,0),(8,4,0)]:
 ns=f'F{a}{b}{e}';cells=sorted([(x,y) for x in range(-10,12) for y in range(-10,12) if 0<=x+y<=a and e<=x-y<=e+b]);centers=[(x,y) for x in range(-10,12) for y in range(-10,12) if a-5<=x+y<=5 and e+b-5<=x-y<=e+5];holes={(2,2),(2,-2),(-2,2),(-2,-2)}
 groups={frozenset(p for p in cells if (p[0]-cx,p[1]-cy) in holes) for cx,cy in centers};groups.update(frozenset(p for p in cells if f(*p)==bd) for f,bd in [(lambda x,y:x+y,0),(lambda x,y:x+y,a),(lambda x,y:x-y,e),(lambda x,y:x-y,e+b)])
 forced=set.union(set(),*(set(g) for g in groups if len(g)==1));free=set(cells)-forced;r=11-len(forced);g={(1,-1),(5,3)} if a==8 and b==4 else set(cells)
 pre='set_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof\n'
 def write(mod,imports,body):
  for d in ['dev','formal']:(L/d/(mod+'.lean')).write_text(''.join('import '+i+'\n' for i in imports)+pre+body+'\nend '+ns+'\n')
 body=f'def forced : Finset GridPoint := {fs(sorted(forced))}\ndef free : Finset GridPoint := {fs(sorted(free))}\ndef miss : Finset GridPoint := {fs(sorted(g))}\n'
 for i,p in enumerate(sorted(forced)):
  c=next(c for c in centers if {q for q in cells if (q[0]-c[0],q[1]-c[1]) in holes}=={p})
  c=(c[0]+c[1],c[0]-c[1])
  body+=f'''theorem single{i} : ({{{str(p).replace(' ','')}}} : Finset GridPoint) ∈ groups {a} {b} {e} := by
  have hc : {str(c).replace(' ','')} ∈ centers {a} {b} {e} := by decide
  have hg : collisionGroup {a} {b} {e} {str(c).replace(' ','')} = {{{str(p).replace(' ','')}}} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hc,rfl⟩)
'''
 body+=f'''theorem forced_sub {{Q : Finset GridPoint}} (hh : HitsAll Q (groups {a} {b} {e})) : forced ⊆ Q := by
  have hs : ∀ p ∈ forced, ({{p}} : Finset GridPoint) ∈ groups {a} {b} {e} := by
    intro p hp
    simp only [forced, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with '''+' | '.join('rfl' for _ in forced)+'\n'+''.join(f'    · exact single{i}\n' for i in range(len(forced)))+'''  intro p hp
  obtain ⟨q,hq,hqp⟩ := hh {p} (hs p hp)
  exact (Finset.mem_singleton.mp hqp) ▸ hq
'''
 body+=f'theorem domain_parts : domain {a} {b} {e} = forced ∪ free := by decide\ntheorem parts_disjoint : Disjoint forced free := by decide\ntheorem forced_card : forced.card = {len(forced)} := by decide\n'
 if a==8 and b==4:body+=f'theorem miss_group : miss ∈ groups {a} {b} {e} := by decide\n'
 else:body+=f'theorem miss_group : miss ∈ groups {a} {b} {e} := by\n  have hh : ¬ ({{(0,0)}} : Finset GridPoint) = ∅ := by decide\n  exact False.elim (hh (by decide))\n' if False else ''
 # Use general cut OR unhit with a literal actual boundary group in the first two cases too.
 if not(a==8 and b==4):
  g=set(next(z for z in groups if z));body=body.replace(f'def miss : Finset GridPoint := {fs(cells)}',f'def miss : Finset GridPoint := {fs(sorted(g))}')
  body+=f'theorem miss_group : miss ∈ groups {a} {b} {e} := by decide\n'
 write(ns+'Data',['ForcedBridge'],body)
 pairs=[]
 for add in combinations(sorted(free),r):
  P=forced|set(add);seen={min(P)}
  for _ in range(11):seen|={q for q in P if any(abs(q[0]-p[0])+abs(q[1]-p[1])==1 for p in seen)}
  pairs.append((add,seen if seen!=P else set()))
 mods=[]
 for bi,start in enumerate(range(0,len(pairs),16)):
  m=ns+f'Batch{bi}';mods.append(m)
  write(m,[ns+'Data'],'def pairs'+str(bi)+' : List (Finset GridPoint × Finset GridPoint) := ['+','.join(f'({fs(add)},{fs(sorted(S))})' for add,S in pairs[start:start+16])+']\n'+f'theorem checked{bi} : ∀ es ∈ pairs{bi}, CutGood (forced ∪ es.1) es.2 ∨ Disjoint (forced ∪ es.1) miss := by decide')
 body='def pairs : List (Finset GridPoint × Finset GridPoint) := '+' ++ '.join(f'pairs{i}' for i in range(len(mods)))+'\n'
 body+=f'theorem coverage : free.powersetCard {r} ⊆ (pairs.map Prod.fst).toFinset := by decide\n'
 body+='theorem checks : ∀ es ∈ pairs, CutGood (forced ∪ es.1) es.2 ∨ Disjoint (forced ∪ es.1) miss := by\n  intro es he\n  simp only [pairs, List.mem_append] at he\n'
 # simp produces right associative?
 body+='  rcases he with '+ ' | '.join('hh'+str(i) for i in range(len(mods)))+'\n'+''.join(f'  · exact checked{i} es hh{i}\n' for i in range(len(mods)))
 body+=f'''theorem case_{a}_{b}_{e} : ∀ Q : Finset GridPoint, Q ⊆ domain {a} {b} {e} → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups {a} {b} {e}) := by
  intro Q hQ hc hn hh
  have hf := forced_sub hh
  have hsub : Q \\ forced ⊆ free := by
    intro p hp
    have ht := hQ (Finset.mem_sdiff.mp hp).1
    rw [domain_parts] at ht
    exact (Finset.mem_union.mp ht).resolve_left (Finset.mem_sdiff.mp hp).2
  have hcard : (Q \\ forced).card = {r} := by
    rw [Finset.card_sdiff_of_subset hf, hn, forced_card]
  have he : Q \\ forced ∈ free.powersetCard {r} := Finset.mem_powersetCard.mpr ⟨hsub,hcard⟩
  have hm := List.mem_toFinset.mp (coverage he)
  obtain ⟨es,hes,heq⟩ := List.mem_map.mp hm
  have hu : forced ∪ es.1 = Q := by rw [heq]; exact Finset.union_sdiff_of_subset hf
  have bad := checks es hes
  rw [hu] at bad
  rcases bad with cut | dis
  · exact not_connected_of_cut cut hc
  · obtain ⟨p,hp,hpg⟩ := hh miss miss_group
    exact Finset.disjoint_left.mp dis hp hpg
'''
 if len(mods)==1:
  start=body.index('  simp only [pairs, List.mem_append] at he');end=body.index(f'theorem case_',start)
  body=body[:start]+'  exact checked0 es he\n'+body[end:]
 write(ns+'Case',mods,body)
 (L/(ns+'-plan.txt')).write_text('\n'.join([ns+'Data']+mods+[ns+'Case'])+'\n')
