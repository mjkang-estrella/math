from pathlib import Path
import json,sys,hashlib,re
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');S=R/'packet/src'
N=int(sys.argv[1]); data=json.loads((R/'normalized-trimmed.json').read_text()); rows=data['steps'][:N]
# Compare the Lean evaluation of the actual normalized generator with the copied DIMACS.
log=(R/'logs/dev-NormalizedExport.log').read_text();export=log.split('BEGIN_DIMACS\n')[1].split('END_DIMACS')[0]
assert export.encode()==(R/'normalized.cnf').read_bytes()
(R/'generator-correspondence.json').write_text(json.dumps({'exact_byte_match':True,'sha256':hashlib.sha256(export.encode()).hexdigest(),'units':[[1],[26],[31]],'base_clause_count':14695,'normalized_clause_count':14698},indent=2))
cnf=[[int(x) for x in line.split()[:-1]] for line in export.splitlines()[1:]]
assert len(cnf)==14698 and cnf[-3:]==[[1],[26],[31]]
used=sorted({h for _,_,hs in rows for h in hs if h<=len(cnf)})
known={int(i) for p in S.glob("Inputs*.lean") for i in re.findall(r"theorem inp_(\d+)",p.read_text())}
def cl(c):return '['+','.join(f'({abs(x)-1},{str(x<0).lower()})' for x in c)+']'
def membership(i):
 k=i-1
 if k<3968:
  a,l=divmod(k,64); kind='A' if a<31 else 'X'; l=a%31
  return f'activationGate5 SatVar.{"a" if kind=="A" else "x"} (.{"i" if kind=="A" else "j"} {l}) {l}',f'activation{kind}_mem {l}'
 k-=3968
 if k<3968:return f'spreadGate5 {k//128}',f'spread_mem {k//128}'
 k-=3968
 if k<31:return f'finalGate5 {k}',f'final_mem {k}'
 k-=31
 if k<5766:
  v,l=divmod(k//6,31);return f'closedGate5 {v} {l}',f'closed_mem {v} {l}'
 return None
mods=[]
for off in range(0,len(used),50):
 m=f'NInputs{off//50:03d}';prev=mods[-1] if mods else 'NormalizedLink';mods.append(m)
 out=[f'import {prev}','namespace Percolation.NReplay','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
 for i in used[off:off+50]:
  out += [f'def cl_{i} : CNF.NClause := {cl(cnf[i-1])}',f'theorem inp_{i} (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_{i} := by']
  if i>14695:
   out += [f'  apply holds_decode',f'  apply h',f'  exact List.mem_append_right _ (by decide : decodeClause cl_{i} ∈ normalizedUnits5)']
  else:
   out += ['  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)']
   if i in known:
    out += [f"  exact Percolation.Replay.inp_{i} v hb"]; continue
   g=membership(i)
   if g:out += [f'  exact input_gate ({g[0]}) ({g[1]}) cl_{i} (by decide) v hb']
   else:
    k=i-1-(3968+3968+31+5766)
    if k==0:term='input_nonfull v hb';cc='pts5.map (fun p => (SatVar.x p, true))'
    elif k<=31:term=f'input_omit {k-1} v hb';cc=f'omitClause5 {k-1}'
    else:
     a,p=divmod(k-32,30);p+=int(p>=a);term=f'input_contain {a} {p} (by decide) v hb';cc=f'containClause5 {a} {p}'
    out += [f'  apply holds_decode',f'  have he : decodeClause cl_{i} = ({cc}) := by decide','  rw [he]',f'  exact {term}']
 out+=['end Percolation.NReplay'];(S/(m+'.lean')).write_text('\n'.join(out)+'\n')
def chain(terms):
 p='(by intro d hd; cases hd)'
 for t in reversed(terms):p=f'(hints_cons _ _ _ ({t}) {p})'
 return p
for start in range(0,N,500):
 m=f'NReplay{start//500:03d}';prev=mods[-1];mods.append(m);part=rows[start:start+500]
 out=[f'import {prev}','namespace Percolation.NReplay','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
 for i,c,hs in part:
  out += [f'def cl_{i} : CNF.NClause := {cl(c)}',f'theorem der_{i} (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_{i} :=',f'  CNF.rup_sound cl_{i} [{",".join(f"cl_{h}" for h in hs)}] (by decide) (v ∘ decodeVar) '+chain([f'{"inp" if h<=14698 else "der"}_{h} v h' for h in hs])]
 tag=f'{start//500:03d}';out += [f'def chunk{tag} : List CNF.NClause := [{",".join(f"cl_{i}" for i,_,_ in part)}]',f'theorem chunk_sound{tag} (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk{tag}, CNF.Holds (v ∘ decodeVar) c :=', '  '+chain([f'der_{i} v h' for i,_,_ in part])]
 if start==0:
  out += [f'def prefix{tag} := chunk{tag}',f'theorem prefix_sound{tag} (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix{tag}, CNF.Holds (v ∘ decodeVar) c := chunk_sound{tag} v h']
 else:
  old=f'{start//500-1:03d}';out += [f'def prefix{tag} := prefix{old} ++ chunk{tag}',f'theorem prefix_sound{tag} (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix{tag}, CNF.Holds (v ∘ decodeVar) c := by', '  intro c hc', '  rcases List.mem_append.mp hc with hc | hc',f'  · exact prefix_sound{old} v h c hc',f'  · exact chunk_sound{tag} v h c hc']
 out += ['end Percolation.NReplay'];(S/(m+'.lean')).write_text('\n'.join(out)+'\n')
last=f'{(N-1)//500:03d}'
(S/'NormalizedEndpoint.lean').write_text(f'''import {mods[-1]}
namespace Percolation.NReplay
def NormalizedFrontierUnsat5 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
    (∀ c ∈ prefix{last}, CNF.Holds (v ∘ decodeVar) c)
theorem not_conjecture20_normalized_after{N} (h : NormalizedFrontierUnsat5) : ¬ Conjecture20 := by
  apply not_conjecture20_normalized
  rintro ⟨v,hv⟩
  exact h ⟨v,hv,prefix_sound{last} v hv⟩
#print axioms not_conjecture20_normalized_after{N}
end Percolation.NReplay
''')
if N==len(data['steps']):
 assert rows[-1][1]==[]
 (S/'NormalizedEndpoint.lean').write_text(f'''import {mods[-1]}
namespace Percolation
 theorem generatedNormalizedUnsat5_closed : GeneratedNormalizedUnsat5 := by
  rintro ⟨v,hv⟩
  have h := NReplay.der_{rows[-1][0]} v hv
  obtain ⟨z,hz,_⟩ := h
  cases hz
 theorem noMinimalTwoRound5_closed : NoMinimalTwoRound5 :=
  normalized_unsat_implies_noMinimal5 generatedNormalizedUnsat5_closed
 theorem not_conjecture20_unconditional : ¬ Conjecture20 :=
  not_conjecture20 noMinimalTwoRound5_closed
#print axioms generatedNormalizedUnsat5_closed
#print axioms noMinimalTwoRound5_closed
#print axioms not_conjecture20_unconditional
end Percolation
''')
mods+=['NormalizedEndpoint'];(R/'normalized-order.txt').write_text('\n'.join(mods)+'\n')
(R/'normalized-progress.json').write_text(json.dumps({'generated_steps':N,'replayed_steps':0,'total_steps':len(data['steps']),'used_inputs':len(used),'last_generated_id':rows[-1][0],'next_index_zero_based':N,'next_retained_step_one_based':N+1,'next_lrat_id':(data['steps'][N][0] if N<len(data['steps']) else 0)},indent=2))
print({'generated_steps':N,'used_inputs':len(used),'modules':len(mods),'next_id':(data['steps'][N][0] if N<len(data['steps']) else 0)})
