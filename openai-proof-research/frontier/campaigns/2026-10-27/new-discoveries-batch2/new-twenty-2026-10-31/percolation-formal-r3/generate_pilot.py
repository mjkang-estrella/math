from pathlib import Path
import json
r=Path(__file__).resolve().parent;s=r/'packet/src'
data=json.loads((r/'input-trimmed.json').read_text());rows=data['steps'][:2000];cnf=json.loads((r/'clauses.json').read_text());n=len(cnf)
used=sorted({h for _,_,hs in rows for h in hs if h<=n})
def clause(c):return '['+','.join(f'({abs(z)-1},{str(z<0).lower()})' for z in c)+']'
def gate(k):
 if k<3968:
  a,l=divmod(k,64);src='A' if a<31 else 'X';l=a%31
  return f'activationGate5 SatVar.{"a" if src=="A" else "x"} (.{"i" if src=="A" else "j"} {l}) {l}',f'activation{src}_mem {l}'
 k-=3968
 if k<3968:
  p=k//128;return f'spreadGate5 {p}',f'spread_mem {p}'
 k-=3968
 if k<31:return f'finalGate5 {k}',f'final_mem {k}'
 k-=31
 if k<5766:
  v,l=divmod(k//6,31);return f'closedGate5 {v} {l}',f'closed_mem {v} {l}'
 return None
mods=[]
for start in range(0,len(used),50):
 name=f'Inputs{start//50:03d}';prev=mods[-1] if mods else 'InputLink';mods.append(name)
 out=[f'import {prev}','namespace Percolation.Replay','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
 for i in used[start:start+50]:
  c=clause(cnf[i-1]);out+=[f'def cl_{i} : CNF.NClause := {c}',f'theorem inp_{i} (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_{i} := by']
  g=gate(i-1)
  if g:
   gt,mem=g;out += [f'  exact input_gate ({gt}) ({mem}) cl_{i} (by decide) v h']
  else:
   k=i-1-(3968+3968+31+5766)
   if k==0:term='input_nonfull v h'
   elif k<=31:term=f'input_omit {k-1} v h'
   else:
    v,p=divmod(k-32,30);p=p if p<v else p+1
    term=f'input_contain {v} {p} (by decide) v h'
   out += [f'  exact holds_decode v cl_{i} (by simpa only [cl_{i}, decodeClause, decodeVar, omitClause5, containClause5, pts5, List.map_cons, List.map_nil] using ({term}))']
 out+=['end Percolation.Replay'];(s/(name+'.lean')).write_text('\n'.join(out)+'\n')
for count in (500,2000):
 name=f'Pilot{count}';out=[f'import {mods[-1]}','namespace Percolation.Replay',f'namespace P{count}','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
 for i,c,hs in rows[:count]:
  out+=[f'def cl_{i} : CNF.NClause := {clause(c)}']
  hints='['+','.join(f'cl_{h}' for h in hs)+']'
  proof='(by intro d hd; cases hd)'
  for h in reversed(hs):
   term=f'inp_{h}' if h<=n else f'der_{h}'
   proof=f'(hints_cons _ _ _ ({term} v h) {proof})'
  out += [f'theorem der_{i} (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_{i} :=',f'  CNF.rup_sound cl_{i} {hints} (by decide) (v ∘ decodeVar) {proof}']
 out +=[f'end P{count}','end Percolation.Replay'];(s/(name+'.lean')).write_text('\n'.join(out)+'\n')
(r/'pilot-order.txt').write_text('\n'.join(mods+['Pilot500','Pilot2000'])+'\n')
(r/'pilot-info.json').write_text(json.dumps({'used_input_count':len(used),'input_modules':mods,'last_id':rows[-1][0],'total_additions':len(data['steps'])},indent=2))
print({'used_inputs':len(used),'input_modules':len(mods),'last_id':rows[-1][0]})
