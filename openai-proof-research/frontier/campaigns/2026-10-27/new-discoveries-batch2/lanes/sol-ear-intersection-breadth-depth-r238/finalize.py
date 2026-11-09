from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((L/'scientificbindings.json').read_text())
for r in rows:assert sha(Path(r['original']))==sha(Path(r['copy']))==r['sha256']
for line in (L/'retrieval.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'sha256' in r:
  p=L/'primary'/r['name'];assert sha(p)==r['sha256'];rows.append(dict(original=str(p),copy=str(p),sha256=sha(p),url=r['url']))
  if 'text_sha256' in r:
   p=p.with_suffix('.txt');assert sha(p)==r['text_sha256'];rows.append(dict(original=str(p),copy=str(p),sha256=sha(p),derived_from=r['name']))
(L/'scientificbindings.json').write_text(json.dumps(rows,indent=2)+'\n')
ledger=json.loads((L/'administrative/ledger.json').read_text());context=json.loads((L/'administrative/prior-campaign-context.json').read_text())
assert (ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number'])==(9,39,40)
prov=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scientific_status='HOLD',credit=0,counts=[9,39,40],accepted_titles=[r.get('title') for r in ledger['accepted']],prior_context_top_keys=list(context),guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',caps=dict(AS_MiB=512,group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230),history_scope='750 compact batch top-level reports, immutable reference bindings; no recursive copies',access='Forbidden routes not retried; inaccessible historical intervals parked; no current complete registry clearance')
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
(L/'finalmanifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print('manifest files',len(manifest))
