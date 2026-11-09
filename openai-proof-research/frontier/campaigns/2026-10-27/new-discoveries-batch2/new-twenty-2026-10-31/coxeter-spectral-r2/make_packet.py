from pathlib import Path
import json,hashlib,zipfile,datetime
w=Path(__file__).resolve().parent
src=(w/'ActualSpectra.lean').read_text().replace('end ActualSpectra330264','')
tree=(w/'ActualTrees.lean').read_text().split('theorem connectedG')[1].split('end ActualSpectra330264')[0]
line=(w/'CanonicalLines.lean').read_text().split('def edgeMapG')[1].split('end ActualSpectra330264')[0]
src='import Mathlib.Combinatorics.SimpleGraph.Acyclic\nimport Mathlib.Combinatorics.SimpleGraph.LineGraph\n'+src
src+='\ntheorem connectedG'+tree+'\ndef edgeMapG'+line+'''
theorem intrinsic_line_charpoly :
    (by classical exact (G.lineGraph.adjMatrix ℚ).charpoly) =
    (by classical exact (H.lineGraph.adjMatrix ℚ).charpoly) := by
  rw [intrinsicG, intrinsicH]
  exact line_charpoly

theorem spectral_hypotheses : G.IsTree ∧ H.IsTree ∧
    AG.charpoly = AH.charpoly ∧ CG.charpoly = CH.charpoly :=
  ⟨treeG, treeH, adjacency_charpoly, complement_charpoly⟩
#print axioms intrinsic_line_charpoly
#print axioms spectral_hypotheses
end ActualSpectra330264
'''
src+='\n'+(w/'GroupSemantics.lean').read_text()+'\n'+(w/'AutomatonCertificate.lean').read_text()
imports=[];body=[]
for ln in src.splitlines():
 if ln.startswith('import '):
  if ln not in imports:imports.append(ln)
 else:body.append(ln)
(w/'PartialEndpoint.lean').write_text('\n'.join(imports+body)+'\n')
files=['PartialEndpoint.lean','spectral_candidate.json','exact_spectra.json','similarity.json','PROOF-330264.md','FORMAL-GAPS.md','source-comparison.md','GroupSemantics.lean','ActualTrees.lean','ActualSpectra.lean','CanonicalLines.lean','AutomatonCertificate.lean','check.py','README-replay.txt','replay-receipt.json','replay.log','SUMMARY.md','results.json','research-notes.md','dependency-hashes.json','input-verification.json','make_similarity.py','generate_spectral.py','generate_trees.py','generate_lines.py','make_packet.py','hash_dependencies.py']
files += [str(p.relative_to(w)) for p in (w/'sources').iterdir() if p.suffix in {'.pdf','.txt','.json'}]
manifest={f:hashlib.sha256((w/f).read_bytes()).hexdigest() for f in files}
manifest['lean_binary']=hashlib.sha256(Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean').read_bytes()).hexdigest()
(w/'packet-manifest.json').write_text(json.dumps({'scope':'PARTIAL, NOT MATHDB ENDPOINT','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','sha256':manifest},indent=2))
with zipfile.ZipFile(w/'330264-r2-PARTIAL.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in files+['packet-manifest.json']:z.write(w/f,f)

x=w/'fresh-extract';x.mkdir(exist_ok=True)
with zipfile.ZipFile(w/'330264-r2-PARTIAL.zip') as z:z.extractall(x)
