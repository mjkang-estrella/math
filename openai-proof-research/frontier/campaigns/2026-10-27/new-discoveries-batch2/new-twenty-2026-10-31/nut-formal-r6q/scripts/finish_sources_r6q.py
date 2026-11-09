import json
from pathlib import Path
r=Path(__file__).resolve().parents[1];supports=json.loads((r/'new-supports.json').read_text())
for sp in supports:
 k=sp['index'];name=f'FiniteSupport{k:03}';f=r/'formal'/(name+'.lean');s=f.read_text();s=s[:s.rfind('end Nut8.')]
 s+=f'theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 {sp["code"]} (e (p i)).val (e i).val = true := by\n  decide +kernel\n'
 s+=f'theorem verified : ∀ A ∈ signedCatalogue {sp["code"]} e p, ¬ (A.det = 0 ∧ ∀ i, A.adjugate i i ≠ 0) := by\n  rw [enumeration]\n  intro A hm\n  simp only [matrices, Finset.mem_insert, Finset.mem_singleton] at hm\n  rcases hm with '+ ' | '.join('rfl' for n in sp['ids'])+'\n'
 for n in sp['ids']:s+=f'  · exact NewCertificates{n//32:04}.obstruction{n}\n'
 s+=f'end Nut8.{name}\n';s=s.replace('namespace Nut8.', 'set_option maxRecDepth 4096\nnamespace Nut8.', 1);f.write_text(s)
lines=[f'import FiniteSupport{s["index"]:03}' for s in supports]+['set_option maxRecDepth 4096','namespace Nut8','theorem per_support : PerSupport := by','  apply per_support_of_signed_catalogues','  intro code hc','  simp only [GraphClosure7_000.targets, List.mem_cons, List.mem_singleton] at hc','  rcases hc with '+' | '.join('rfl' for s in supports)]
for sp in supports:
 ns=f'FiniteSupport{sp["index"]:03}';lines.append(f'  · exact ⟨{ns}.e, {ns}.p, {ns}.tree, {ns}.verified⟩')
lines.append('end Nut8');(r/'formal/PerSupport.lean').write_text('\n'.join(lines)+'\n')
