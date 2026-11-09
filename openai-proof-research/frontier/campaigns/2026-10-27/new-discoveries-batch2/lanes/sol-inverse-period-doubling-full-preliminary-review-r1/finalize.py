from pathlib import Path
import hashlib,json,datetime,shutil
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
A=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md')
shutil.copyfile(A,L/'administrative/ancestor-AGENTS.md')
coverage=[]
for r in json.loads((L/'bindings.json').read_text()):
 n=Path(r['original']).name
 if n in ['current-stip8.pdf','stip8.txt','durand.pdf','durand.txt','merta-bs.pdf','merta-bs.txt','merta-general.pdf','merta-general.txt','logic.pdf','logic.txt','PROOF.md']:
  coverage.append(r)
(L/'source-coverage.json').write_text(json.dumps({'body_hash_bindings':coverage,'body_coverage':'Exact sections, URLs, version chronology and unread intervals in review.md; text copies were frozen before reading. Fresh Durand extraction derives from the frozen PDF.','new_retrievals':'current-retrieval.json'},indent=2)+'\n')
guard=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
pro={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'solo independent preliminary reviewer','counts_unchanged':[9,39,40],'gates':{'SOURCE':'PASS','MATH':'PASS','SUBSTANTIVE':'PASS preliminary','NOVELTY':'HOLD','FORMALFEASIBILITY':'HOLD'},'guard':str(guard),'guard_sha256':h(guard),'caps':{'AS_MiB':512,'sampled_groupRSS_MiB':512,'CPU_s':210,'wall_s':230},'attribution':'Parent dispatch: root suggested first-threshold/pumping; r240 observations; r242 actual proof; this lane independent reconstruction and diagnostics.','administrative_snapshot_hashes':{str(p.relative_to(L)):h(p) for p in (L/'administrative').iterdir()},'scientific_bindings':['bindings.json','library-bindings.json'],'separate_verifier':'verify.py','acceptance':'HOLD; root alone accepts/counts'}
(L/'provenance.json').write_text(json.dumps(pro,indent=2)+'\n')
manifest={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'manifest_files':len(manifest),'excluded':['manifest.json','verification-receipt.json']}))
