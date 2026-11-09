from pathlib import Path
import json,collections
w=Path(__file__).resolve().parent;c=json.loads((w.parent/'fresh-corpus-r10/spectral_candidate.json').read_text());s=(w/'SpectralDefinitions.lean').read_text().replace('end ActualSpectra330264','');s='import Mathlib.Combinatorics.SimpleGraph.Acyclic\nimport Mathlib.Tactic.FinCases\n'+s
for k in ['G','H']:
 E=c[k.lower()];seen={0};q=collections.deque([0]);ps=[]
 while q:
  u=q.popleft()
  for a,b in E:
   v=b if a==u else a if b==u else -1
   if v>=0 and v not in seen:seen.add(v);q.append(v);ps.append((u,v))
 s+=f'\ntheorem connected{k} : {k}.Connected := by\n  apply (SimpleGraph.connected_iff_exists_forall_reachable {k}).mpr\n  refine ⟨0, ?_⟩\n  have r0 : {k}.Reachable 0 0 := SimpleGraph.Reachable.refl _\n'
 for u,v in ps:s+=f'  have r{v} : {k}.Reachable 0 {v} := r{u}.trans (SimpleGraph.Adj.reachable (show {k}.Adj {u} {v} from by decide +kernel))\n'
 s+='  intro v\n  fin_cases v\n'
 for v in range(19):s+=f'  · exact r{v}\n'
 s+=f'theorem tree{k} : {k}.IsTree := by\n  apply (SimpleGraph.isTree_iff_connected_and_card).mpr\n  refine ⟨connected{k}, ?_⟩\n  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]\n  decide +kernel\n#print axioms tree{k}\n'
s+='end ActualSpectra330264\n';(w/'ActualTrees.lean').write_text(s)
