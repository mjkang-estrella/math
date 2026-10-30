import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def write(n,v):(L/n).write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert sha(guard.read_bytes())=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
contexts=[]
for p in [B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',L.parents[5]/'AGENTS.md',B/'AGENTS.md']:
 b=p.read_bytes();contexts.append(dict(path=str(p),bytes=len(b),sha256=sha(b),role='mutable context outside science' if p.name=='NEXT.md' else 'governing context'))
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
for r in http:
 if 'sha256' in r:assert sha((L/'sources'/r['name']).read_bytes())==r['sha256']
queries=[]
for p in L.glob('history-query-*.json'):
 j=json.loads(p.read_bytes());queries.append(dict(path=p.name,pattern=j['pattern'],full_body_count=j['full_body_count'],hits=j['hits'],cutoff=j['cutoff'],original_r111_r113=j['original_r111_r113']))
assert all(j['original_r111_r113'] for j in queries)
checks=json.loads((L/'checks.json').read_bytes());assert checks['result'].startswith('PASS') and not checks['universal_source_result']
write('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),local_research_date='2026-10-29 America/Los_Angeles',result='zero; full Sun A224416(i) least-prime bound unresolved',contexts=contexts,http=http,history=dict(delta='history-delta.json',queries=queries,original_body_role_scope=True,limits='Qualified retained original science, generated echoes excluded by role; not universal semantic coverage'),registries=dict(receipt='registry-screen.json',omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',gaps=['aa026->a19a capped300','a19a->490f capped300','retained narrow walks do not clear omitted paths','no global semantic body audit']),primary_scope=dict(target='Sun OEIS A224416 COMMENTS(i) least prime <=n^2+n+5',latest_seki='2609.10526v1; 2026-09-09',seki_coverage='actual PDF pp1-6, especially Section4.1; current arXiv metadata and author bibliography',journal='not established; author bibliography lists preprint',companion='Nguyen-Dang Valency W_mep2xkcu_v2, published 2026-10-27',companion_coverage='Theorem E and actual Catalan proof section equations44-50, Lemma5.3, block exclusions and all-degree assembly; external dependencies and verifier not independently replayed',public_counterpart_scope='all-n symmetric group, not least-prime bound',chronology='public October27 counterpart precedes October30UTC investigation; not our credited publication'),checks=checks,guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=536870912,group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,environment=['OPENBLAS_NUM_THREADS=1','OMP_NUM_THREADS=1','PYTHONDONTWRITEBYTECODE=1'],qualification='Group RSS sampled, not continuous; no claim excluding unsampled transients; caps unchanged',final_guard_log='checks-final.log'),failures=['checks.log: initial independent check reduced already-reduced coefficients; assertion failed; corrected to rebuild original coefficients','fetch.log: Unicode URL encoding failure; percent-encoded author URL succeeded','PDF conversion emitted font mismatch warning; extracted text read','web open Valency v1: Internal Error/access not available; current v2 HTTP succeeded'],access_controls='No403/429/challenge observed, none bypassed',credit=0,external_actions=False,scientific_exclusions=['context-NEXT.md','derived manifests/verification receipts and terminal log']))
excluded={'finalmanifest.json','scientific-freeze.json','manifest-verification.json','verify.log','finalize.log'}
payload={str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded}
science={p:h for p,h in payload.items() if p!='context-NEXT.md'}
write('scientific-freeze.json',dict(algorithm='sha256',files=science,excluded_mutable_context=['context-NEXT.md'],qualification='No PROOF.md; zero nomination'))
payload['scientific-freeze.json']=sha((L/'scientific-freeze.json').read_bytes())
write('finalmanifest.json',dict(algorithm='sha256',files=payload,excluded_derived_outputs=sorted(excluded-{'scientific-freeze.json','finalmanifest.json'})))
print('Finalized zero-result payload.')
