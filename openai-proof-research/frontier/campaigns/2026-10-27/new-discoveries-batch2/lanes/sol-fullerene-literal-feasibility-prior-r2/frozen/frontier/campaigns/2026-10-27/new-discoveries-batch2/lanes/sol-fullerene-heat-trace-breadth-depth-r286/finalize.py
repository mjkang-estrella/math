from pathlib import Path
import json,hashlib,subprocess,sys
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
# Last report corrections and explicit bounded body-filter distinctions.
for name in ['SCOUTING.md']:
 p=L/name;s=p.read_text().replace('Pablo M. Berná','Andrea García').replace('Ganikhodjaev–Mukhamedov–Rozikov','Ganikhodzhaev–Rozikov')
 s+='\nThe additional cached Coutinho matches concern normalized-Laplacian perfect transfer on a 17-vertex tree and combinatorial-Laplacian peak transfer on non-star trees. Their actual cached settling proof bodies were inspected; neither is adjacency-Hamiltonian perfect transfer with an asymptotic edge/diameter exponent. The Carli Silva theta-representation convexity proof dossier is unrelated to a heat-trace collision. No credit comes from these near matches.\n\nDate fidelity: arXiv identifier 1003.3127v1 is a 2010 deposition; the retrieved PDF itself prints November 1, 2018. Both are retained; no uninspected 2010-versus-2018 text identity or chronological priority inference is made.\n'
 p.write_text(s)
p=L/'independent-check-output.json';r=subprocess.run([sys.executable,str(L/'independent_check.py')],capture_output=True,text=True,check=True);p.write_text(r.stdout)
pro=json.loads((L/'provenance.json').read_text());guard=Path(pro['guard']);pro['guard_sha256']=sha(guard);pro['final_check']='independent-check-output.json';(L/'provenance.json').write_text(json.dumps(pro,indent=2))
manifest={str(p.relative_to(L)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
(L/'MANIFEST.json').write_text(json.dumps(manifest,indent=2));print('Finalized',len(manifest),'files; independent checker PASS')
