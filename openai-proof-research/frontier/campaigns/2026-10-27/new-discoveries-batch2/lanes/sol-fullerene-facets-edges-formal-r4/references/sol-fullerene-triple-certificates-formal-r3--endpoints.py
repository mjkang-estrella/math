from pathlib import Path
import json
L=Path(__file__).resolve().parent
raw=json.loads((L/'frozen/rational-realizations.json').read_text())
for tag in ['G','H']:
 t=[f'import All{tag}',f'import Bindings{tag}',f'import Listed{tag}','import CompletionCore','set_option autoImplicit false','set_option warningAsError true','noncomputable section','namespace FullereneGeometry','open TripleCertificates',f'theorem complete_triples_{tag} (ids : Fin 3 → Fin 32)',f' (hi : LinearIndependent ℝ (fun k => q{tag} (ids k))) (x : E)',f' (hf : x ∈ poly q{tag}) (ha : ∀ k, dot (q{tag} (ids k)) x=1) : x ∈ Set.range p{tag} :=',f' complete_real q{tag} p{tag} A{tag} D{tag} P{tag} records{tag} Dpos{tag} qbind{tag} pbind{tag} checked{tag} coverage{tag} ids hi x hf ha',f'theorem listed_vertices_{tag} (v : Fin 60) :',f' p{tag} v ∈ poly q{tag} ∧ ∃ ids : Fin 3 → Fin 32,',f' (∀ k, dot (q{tag} (ids k)) (p{tag} v)=1) ∧',f' (∀ y : E, (∀ k, dot (q{tag} (ids k)) y=1) → y=p{tag} v) := by',f' rw [← pbind{tag} v]',' fin_cases v']
 for n,ids in enumerate(raw[tag]['dual_facets']):
  i,j,k=ids
  t.append(f' · exact listed_real q{tag} A{tag} D{tag} (P{tag} {n}) Dpos{tag} qbind{tag} {i} {j} {k} listed{tag}{n:02d}.2.1 listed{tag}{n:02d}.2.2')
 t += [f'theorem complete_vertices_{tag} : (poly q{tag}).extremePoints ℝ = Set.range p{tag} :=',f' complete_vertices_of_triple_certificates q{tag} p{tag} complete_triples_{tag} listed_vertices_{tag}','end FullereneGeometry']
 (L/f'Complete{tag}.lean').write_text('\n'.join(t)+'\n')
 t=[f'import Complete{tag}','import Hulls','noncomputable section','namespace FullereneGeometry',f'theorem hull_{tag} : poly q{tag} = convexHull ℝ (Set.range p{tag}) :=',f' hull_of_complete_vertices q{tag} compact_{tag} p{tag} complete_vertices_{tag}',f'theorem section_hull_{tag} (i : Fin 32) :',f' facetSection q{tag} i = convexHull ℝ {{x ∈ Set.range p{tag} | dot (q{tag} i) x=1}} :=',f' section_hull_of_complete_vertices q{tag} compact_{tag} p{tag} complete_vertices_{tag} i','end FullereneGeometry']
 (L/f'Hull{tag}.lean').write_text('\n'.join(t)+'\n')
print('actual G/H completion and hull targets generated; unproved until replay')
