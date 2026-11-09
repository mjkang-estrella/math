import pathlib,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent;B=L.parent.parent;R=L.parents[5]
H=lambda b:hashlib.sha256(b).hexdigest()
for p,name in [(B/'AGENTS.md','batch-AGENTS.md'),(R/'AGENTS.md','ancestor-AGENTS.md')]:
 (L/'admin'/name).write_bytes(p.read_bytes())
bindings=json.loads((L/'bindings.json').read_text())+json.loads((L/'screen-bindings.json').read_text())
for b in bindings:assert H(pathlib.Path(b['original']).read_bytes())==b['sha256'],b['original']
local=[]
for name in ['live-0.txt','live-1.txt','live-2.pdf','ancestor2020.txt','author-successors.xml']:
 p=L/name;data=p.read_bytes();local.append(dict(copy=name,sha256=H(data),bytes=len(data)))
(L/'local-source-bindings.json').write_text(json.dumps(local,indent=2)+'\n')
ledger=json.loads((L/'admin/ledger.json').read_text())
context=json.loads((L/'admin/prior-campaign-context.json').read_text())
prov=dict(lane=L.name,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='HOLD_NO_RESOLUTION',discovery_nomination=False,counts={k:ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']},prior_context_keys=list(context),primary='https://arxiv.org/pdf/2311.09054v2',primary_date='2026-05-04',ancestor='https://ajc.maths.uq.edu.au/pdf/76/ajc_v76_p183.pdf',public_registry_head='UNKNOWN; denied routes parked and not retried',scientific_freeze='bindings.json, screen-bindings.json, access.json and ancestor-binding.json; hashes before interpretation and after; immutable sources reused',administrative='snapshots only; no immutability assertion about live shared admin',limits=dict(AS_MiB=512,group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230,cap_raises=False),guard=str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),guard_sha256=H((L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py').read_bytes()),children=False,external_mutations=False,limitations=['No current registry clearance','No all-ranges selection proof','No exhaustive orientation counterexample','No novelty assertion for helper identities','Bounded cached corpus only'])
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
manifest=[]
for p in sorted(L.rglob('*')):
 if not p.is_file() or p.name in ['MANIFEST.json','verification-receipt.json']:continue
 b=p.read_bytes();manifest.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=H(b)))
(L/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Final manifest entries:',len(manifest))
