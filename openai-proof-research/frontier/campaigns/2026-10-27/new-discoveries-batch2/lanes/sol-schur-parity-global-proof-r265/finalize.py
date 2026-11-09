from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
prov=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='HOLD: universal source lower bound unresolved',credit=0,counts=dict(additional=9,total=39,next=40,changed=False),guard=dict(path=str(guard),sha256=h(guard),AS_bytes=536870912,groupRSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,cap_raises=False),scientific_bindings='bindings.json',new_primary_bindings='primary-followup.json',retrievals='retrieval.json',checks=['check-runs.json','scientific-verification.json','block-identity.json','mechanisms.json','interval-exchange.json','plateau.json'],current_proof_registry_head=None,pinned_registry_head='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',prior_screen='bounded actual primary-body reading; no current registry or worldwide priority clearance',children=False,git=False,browser=False,public_mutations=False,lean=False,manuscript=False,independent_agent_review=False,scientific_outcome='Known source attainment verified for all n>=12; exchange and structural blow-up obstructions only')
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['final-manifest.json','final-verification.json']:
  files.append(dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=h(p)))
(L/'final-manifest.json').write_text(json.dumps(dict(excludes=['final-manifest.json','final-verification.json'],files=files),indent=2)+'\n')
print(dict(files=len(files),manifest_sha256=h(L/'final-manifest.json')))
