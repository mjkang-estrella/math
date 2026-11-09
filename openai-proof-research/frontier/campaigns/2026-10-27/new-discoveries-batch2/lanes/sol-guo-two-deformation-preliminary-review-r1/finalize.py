from pathlib import Path
import json,hashlib,shutil,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
B=L.parent.parent
shutil.copyfile(B/'AGENTS.md',L/'administrative'/'batch-AGENTS.md')
shutil.copyfile(B.parents[3]/'AGENTS.md',L/'administrative'/'ancestor-AGENTS.md')
freeze=json.loads((L/'freeze.json').read_text())
sources=[]
for row in freeze['scientific']:
 p=L/row['copy']
 assert h(p)==h(Path(row['original']))==row['sha256']
 sources.append(row)
for row in json.loads((L/'search-provenance.json').read_text()):
 if 'sha256' in row:
  assert h(L/row['copy'])==h(Path(row['original']))==row['sha256'];sources.append(row)
receipts=[json.loads(v) for v in (L/'frozen/http.jsonl').read_text().splitlines() if v.strip()]
selected=[r for r in receipts if r.get('file') in ['factors.pdf','schilling-warnaar.pdf','divisibility.pdf','guoschlosser.pdf','microscope.pdf','sunv4.pdf']]
(L/'provenance.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scientific_before_after=sources,inherited_primary_http_receipts=selected,administrative='snapshots only; batch and ancestor instructions separately named',freeze_policy='selected files only; before scientific content reading; no recursive historical duplication',guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',limits=dict(AS_bytes=536870912,groupRSS_bytes=536870912,CPU_seconds=210,wall_seconds=230),status='No shared count or acceptance mutation'),indent=2)+'\n')
manifest={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Manifest finalized:',len(manifest),'files; excludes itself and verification-receipt.json')
