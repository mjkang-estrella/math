from pathlib import Path
import json
p=Path(__file__).resolve().parent.parent
r=p.parent
coverage=json.loads((r/'xor-magic-focused-r1/outputs/base-coverage.json').read_text())
modules=[]
for N,types in coverage.items():
 n=int(N).bit_length()-1; N=int(N)
 for typ,entries in types.items():
  for degree,info in entries.items():
   d=int(degree); name=f'Base{N}{typ.title()}{d}'; modules.append(name)
   source=r/'xor-magic-focused-r1'/info['file']
   data=json.loads(source.read_text()); edges={tuple(sorted(e)) for e in data['edges']}
   if info['complement']: edges={(u,v) for u in range(N) for v in range(u+1,N)}-edges
   masks=[sum(1<<v for v in range(N) if tuple(sorted((u,v))) in edges) for u in range(N)]
   parent=[0]*N; rank=[None]*N; rank[0]=0; queue=[0]
   for u in queue:
    for v in range(N):
     if masks[u]>>v&1 and rank[v] is None:
      parent[v]=u; rank[v]=rank[u]+1; queue.append(v)
   assert len(queue)==N
   vec=lambda xs:'!['+','.join(map(str,xs))+']'
   s=f"""import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.{name}
def masks : Fin {N} → ℕ := {vec(masks)}
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin {N} → Fin {N} := {vec(parent)}
def ranks : Fin {N} → ℕ := {vec(rank)}
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree {d} := by\n  change ∀ v, graph.degree v = {d}\n  decide
theorem label_bijective : Function.Bijective (binaryLabel {n}) := by decide
noncomputable def labels : Fin {N} ≃ Bits {n} := Equiv.ofBijective (binaryLabel {n}) label_bijective
theorem zero_sum : ∀ v, {'labels v + ' if typ=='closed' else ''}(∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : {'ClosedMagic' if typ=='closed' else 'OpenMagic'} graph {n} := ⟨connected, labels, zero_sum⟩
theorem exists_literal : {'ClosedExists' if typ=='closed' else 'OpenExists'} {n} {d} :=
  ⟨Fin {N}, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.{name}
"""
   (p/'formal'/f'{name}.lean').write_text(s)
(p/'modules.json').write_text(json.dumps(['Literal','Certificates']+modules,indent=2))
