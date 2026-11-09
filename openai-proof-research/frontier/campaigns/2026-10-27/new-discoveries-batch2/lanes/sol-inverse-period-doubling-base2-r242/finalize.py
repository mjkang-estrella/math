from pathlib import Path
import json,hashlib,subprocess,sys,datetime
L=Path(__file__).resolve().parent
r=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True)
(L/'check-replay.json').write_text(json.dumps({'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2));assert r.returncode==0
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
snap={str(p.relative_to(L)):h(p) for p in (L/'administrative').iterdir() if p.is_file()}
(L/'administrative-snapshot-hashes.json').write_text(json.dumps(snap,indent=2))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
(L/'provenance.json').write_text(json.dumps({'status':'complete ordinary proof proposed; all acceptance/novelty HOLD pending root review','counts':[9,39,40],'guard':str(guard),'guard_sha256':h(guard),'caps':{'AS_MiB':512,'groupRSS_MiB':512,'CPU_s':210,'wall_s':230},'date_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'new_primary_sources':['https://arxiv.org/pdf/1102.3698','https://arxiv.org/pdf/1903.03504v1'],'scientific_bindings':'bindings.json','proof':'PROOF.md'},indent=2))
manifest={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2));print('manifest entries',len(manifest))
