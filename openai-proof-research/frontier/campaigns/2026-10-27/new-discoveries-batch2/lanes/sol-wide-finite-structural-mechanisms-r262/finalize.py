from explore import *
G=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
status=dict(utc=str(datetime.datetime.now(datetime.timezone.utc)),counts=dict(additional=9,total=39,next=40,changed=False),status='unresolved; eligibility HOLD; no ordinary full outcome',guard=dict(path=str(G),sha256=digest(G),AS=536870912,groupRSS=536870912,CPU_seconds=210,wall_seconds=230,cap_raises=False),current_registry_head=None,pinned_registry_head='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',source_bindings='bindings.jsonl',retrievals='retrieval.jsonl',administrative_and_frozen_reports='provenance.json',history='history-bindings.json',semantic_history='semantic-history.json',failures=['mechanism2-guard.json','exact-checks.json'],independent_review=False,acceptance_credit=0,screened_families=16,ranked_leads=1,external_mutations=False,children=False,lean=False,manuscript=False)
(L/'provenance-status.json').write_text(json.dumps(status,indent=2))
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['final-manifest.json','final-verification.json']:
  files.append(dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=digest(p)))
(L/'final-manifest.json').write_text(json.dumps(dict(excludes=['final-manifest.json','final-verification.json'],files=files),indent=2))
print(json.dumps(dict(manifest_entries=len(files),status='written; separate verification next')))
