import json,pathlib
P=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((P.parent/'expanded-corpus-r153/outputs/pure-dag.json').read_text())
nodes=r['nodes'];size=4
assert len(nodes)==2328
assert len({tuple(tuple(row) for row in n['graph']) for n in nodes})==2328
assert sum(len(n['children']) for n in nodes)==9846
for start in range(0,len(nodes),size):
 c=start//size;end=min(start+size,len(nodes))
 out=[f'import {"RawClosure" if c==0 else f"Closure{c-1:03}"}', 'namespace RawCert','open Delta153 RawClosure','set_option maxRecDepth 8192','set_option maxHeartbeats 4000000']
 for i in range(start,end):
  n=nodes[i];cs=n['children'];assert all(j<i for x,j in cs)
  children=', '.join(f'({x}, node{j})' for x,j in cs)
  out += [f'def node{i} : Graph := {n["graph"]}',f'theorem lower{i} : ∀ h, Pure node{i} h → 11 ≤ h.length := by',f'  apply indexed_extend node{i} [{children}] (by decide +kernel) (by decide +kernel)', '  intro k hk']
  if not cs:out+=['  simp at hk']
  else:
   out+=['  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk' if len(cs)>1 else '  simp only [List.mem_singleton] at hk']
   out += ['  rcases hk with '+' | '.join(['rfl']*len(cs))]
   out += [f'  · exact lower{j}' for x,j in cs]
 graphs=', '.join(f'node{i}' for i in range(start,end));arcs=sum(len(nodes[i]['children']) for i in range(start,end))
 out += [f'def entries{c} : List Graph := [{graphs}]',f'theorem entries_count{c} : entries{c}.length = {end-start} := by decide +kernel',f'theorem arc_count{c} : (entries{c}.map (fun g => ((verts g).filter (wye g)).length)).sum = {arcs} := by decide +kernel','end RawCert']
 (P/f'lean/Closure{c:03}.lean').write_text('\n'.join(out)+'\n')
counts=', '.join(f'entries{c}.length' for c in range(582))
arcs=', '.join(f'(entries{c}.map (fun g => ((Delta153.verts g).filter (Delta153.wye g)).length)).sum' for c in range(582))
out=['import Closure581','namespace RawCert','set_option maxRecDepth 16384','set_option maxHeartbeats 4000000', 'theorem canonical_original_lower : ∀ h, RawClosure.Pure Delta153.original h → 11 ≤ h.length := by', '  have eq : Delta153.original = node2327 := by decide +kernel','  rw [eq]','  exact lower2327',f'theorem certificate_entry_count : ([{counts}] : List Nat).sum = 2328 := by',f'  simp only [{", ".join(f"entries_count{c}" for c in range(582))}]','  decide +kernel',f'theorem certificate_legal_arc_count : ([{arcs}] : List Nat).sum = 9846 := by',f'  simp only [{", ".join(f"arc_count{c}" for c in range(582))}]','  decide +kernel','#print axioms canonical_original_lower','#print axioms certificate_legal_arc_count','end RawCert']
(P/'lean/RawResult.lean').write_text('\n'.join(out)+'\n')
(P/'logs/certificate-counts.json').write_text(json.dumps({'states':2328,'arcs':9846,'root':r['root'],'chunks':582})+'\n')
