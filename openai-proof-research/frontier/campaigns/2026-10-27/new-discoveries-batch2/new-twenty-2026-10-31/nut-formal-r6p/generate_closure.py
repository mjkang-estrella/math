from pathlib import Path
import re
r=Path(__file__).resolve().parent
for n in range(1,8):
 ps=sorted((r/'formal').glob(f'GraphClosure{n}_*.lean'))
 src='([0] : List ℕ)' if n==1 else f'GraphClosure{n-1}_000.targets'
 out=''.join('import '+p.stem+'\n' for p in ps)
 if n>1:out+=f'import GraphClosure{n-1}_000\n'
 out+='namespace Nut8\n'
 out+=f'theorem catalogue_closed_{n} (a : ℕ) (ha : a ∈ {src}) :\n    ∃ cs, extensionClosed {n} a GraphClosure{n}_000.targets cs = true := by\n'
 out+=f'  simp only [{"List.mem_singleton" if n==1 else f"GraphClosure{n-1}_000.targets, List.mem_cons, List.not_mem_nil, or_false"}] at ha\n'
 entries=[]
 for p in ps:
  entries += [(int(idx),p.stem,idx) for idx in re.findall(r'theorem closed(\d+) :',p.read_text())]
 entries.sort()
 if n==1:out+='  subst a\n  exact ⟨GraphClosure1_000.certificates0, GraphClosure1_000.closed0⟩\n'
 else:
  out+='  rcases ha with '+ ' | '.join(['rfl']*len(entries))+'\n'
  for _,mod,idx in entries:out+=f'  · exact ⟨{mod}.certificates{idx}, {mod}.closed{idx}⟩\n'
 out+='end Nut8\n';(r/'formal'/f'CatalogueClosure{n}.lean').write_text(out)
