from pathlib import Path
import json,hashlib,re,sys,zipfile
R=Path(sys.argv[1]); P=R/'packet'; S=P/'src'
rows=json.loads((P/'normalized-trimmed.json').read_text())['steps']
stop=int(sys.argv[2]); start=12500
clauses={int(line.split()[0]):[] for line in []}
cnf=[[int(x) for x in l.split()[:-1]] for l in (P/'normalized.cnf').read_text().splitlines() if l and l[0] not in 'cp']
clauses={i+1:c for i,c in enumerate(cnf)}; clauses.update({i:c for i,c,h in rows})
def cost(row):
 i,c,hs=row
 return 1+len(c)+sum(1+len(clauses[h]) for h in hs)*(1+len(c)/8)
def literal(c):return '['+','.join(f'({abs(x)-1},{str(x<0).lower()})' for x in c)+']'
def hints(hs):return '['+','.join(f'cl_{h}' for h in hs)+']'
def chain(ts):
 p='(by intro d hd; cases hd)'
 for t in reversed(ts):p=f'(hints_cons _ _ _ ({t}) {p})'
 return p
header=['namespace Percolation.NReplay','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
order=(P/'module-order.txt').read_text().splitlines();prev='NReplay024';prefix='prefix024';sound='prefix_sound024';front=(P/'replay-frontiers.tsv').read_text();stats=[];k=0
while start<stop:
 end=start;budget=0
 while end<stop and end-start<250 and (end==start or budget+cost(rows[end])<250000):
  budget+=cost(rows[end]);end+=1
 part=rows[start:end];tag=f'R5_{k:04d}';defs='Defs'+tag
 out=[f'import {prev}']+header+[f'def cl_{i} : CNF.NClause := {literal(c)}' for i,c,hs in part]+['end Percolation.NReplay']
 (S/(defs+'.lean')).write_text('\n'.join(out)+'\n');order.append(defs);prev=defs
 # Checks sized by aggregate weighted hints, with at most 60 rows.
 off=0;j=0
 while off<len(part):
  to=off;b=0
  while to<len(part) and to-off<60 and (to==off or b+cost(part[to])<70000):b+=cost(part[to]);to+=1
  name=f'Check{tag}_{j:02d}'
  out=[f'import {prev}']+header+[f'theorem rc_{i} : CNF.rup cl_{i} {hints(hs)} = true := by decide' for i,c,hs in part[off:to]]+['end Percolation.NReplay']
  (S/(name+'.lean')).write_text('\n'.join(out)+'\n');order.append(name);prev=name;off=to;j+=1
 name='Replay'+tag;out=[f'import {prev}']+header
 for i,c,hs in part:
  out += [f'theorem der_{i} (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_{i} :=',f'  CNF.rup_sound cl_{i} {hints(hs)} rc_{i} (v ∘ decodeVar) '+chain([f'{"inp" if h<=14698 else "der"}_{h} v h' for h in hs])]
 chunk='chunk'+tag;newprefix='prefix'+tag;newsound='prefix_sound'+tag
 out += [f'def {chunk} : List CNF.NClause := {hints([i for i,c,hs in part])}',f'theorem chunk_sound{tag} (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ {chunk}, CNF.Holds (v ∘ decodeVar) c :=', '  '+chain([f'der_{i} v h' for i,c,hs in part]),f'def {newprefix} := {prefix} ++ {chunk}',f'theorem {newsound} (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ {newprefix}, CNF.Holds (v ∘ decodeVar) c := by','  intro c hc','  rcases List.mem_append.mp hc with hc | hc',f'  · exact {sound} v h c hc',f'  · exact chunk_sound{tag} v h c hc','end Percolation.NReplay']
 (S/(name+'.lean')).write_text('\n'.join(out)+'\n');order.append(name);prev=name;prefix=newprefix;sound=newsound
 front+=f'{name}\t{end}\t{rows[end-1][0]}\t{rows[end][0] if end<len(rows) else 0}\n';stats.append(dict(module=name,start=start,end=end,cost=budget,checks=j));start=end;k+=1
endpoint='EndpointR5'
(S/(endpoint+'.lean')).write_text(f'''import {prev}
namespace Percolation.NReplay
def RemainingSuffixUnsatR5 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
    (∀ c ∈ {prefix}, CNF.Holds (v ∘ decodeVar) c)
theorem not_conjecture20_normalized_after{stop} (h : RemainingSuffixUnsatR5) : ¬ Conjecture20 := by
  apply not_conjecture20_normalized
  rintro ⟨v,hv⟩
  exact h ⟨v,hv,{sound} v hv⟩
#print axioms not_conjecture20_normalized_after{stop}
end Percolation.NReplay
''');order.append(endpoint)
audit=(S/'AuditR4.lean').read_text().replace('import NormalizedEndpoint','import EndpointR5').replace('"AuditR4"','"AuditR5"')
audit=re.sub(r'  let localModules : Array String := #[^\n]+','  let localModules : Array String := #'+json.dumps(order+['AuditR5'],separators=(',',':')),audit)
(S/'AuditR5.lean').write_text(audit);order.append('AuditR5')
(P/'module-order.txt').write_text('\n'.join(order)+'\n');(P/'replay-frontiers.tsv').write_text(front)
(R/'generation.json').write_text(json.dumps(stats,indent=2))
# Keep all inherited source bytes, including both old endpoints and audits.
manifest=json.loads((R/'inherited-source-comparison.json').read_text())
assert all(hashlib.sha256((P/n).read_bytes()).hexdigest()==h for n,h in manifest.items())
(P/'source-manifest.sha256').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(P))+'\n' for p in sorted(S.glob('*.lean'))))
print({'stop':stop,'modules':len(order),'new_chunks':len(stats),'max_cost':max(x['cost'] for x in stats)})
