from pathlib import Path
import json,collections,re
r=Path(__file__).resolve().parents[1];ss=json.loads((r/'new-supports.json').read_text());rs=json.loads((r/'new-certificates.json').read_text())
for sp in ss:
 i=sp['index'];ns=f'Nut8.FiniteSupport{i:03}';groups=collections.OrderedDict()
 for n in sp['ids']:
  a=rs[n]['matrix'];groups.setdefault(tuple(abs(x) for row in a for x in row),[]).append(n)
 for k,ids in enumerate(groups.values()):
  f=r/'formal'/f'SignedSupport{i:03}_{k//4:03}.lean';s=f.read_text();s=s[:s.rfind('end '+ns)]
  s+=f'theorem checked{k} : ∀ A ∈ signedPatterns (U{k}.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by\n  rw [signed_enumeration{k}]\n  intro A hm\n  simp only [Finset.mem_insert, Finset.mem_singleton] at hm\n  rcases hm with '+ ' | '.join('rfl' for _ in ids)+'\n'
  for n in ids:s+=f'  · exact NewCertificates{n//32:04}.obstruction{n}\n'
  s+=f'end {ns}\n';f.write_text(s)
 f=r/'formal'/f'FiniteSupport{i:03}.lean';s=f.read_text();s=s[:s.index('theorem enumeration')]
 s+=f'theorem verified : ∀ A ∈ signedCatalogue {sp["code"]} e p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by\n  intro A hm\n  obtain ⟨U, hU, hm⟩ := Finset.mem_biUnion.mp hm\n  rw [unsigned_enumeration] at hU\n  simp only [Finset.mem_insert, Finset.mem_singleton] at hU\n  rcases hU with '+ ' | '.join('rfl' for _ in groups)+'\n'
 for k in range(len(groups)):s+=f'  · exact checked{k} A hm\n'
 s+=f'end {ns}\n';f.write_text(s)
print('Obstruction proofs compose locally, without a large union equality')
