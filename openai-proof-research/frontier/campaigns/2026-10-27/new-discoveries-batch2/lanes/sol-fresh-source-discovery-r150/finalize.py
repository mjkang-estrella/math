import json,hashlib,datetime,re
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parents[1];R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
contexts=[]
for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
 p=B/n;b=p.read_bytes();(L/('context-'+n)).write_bytes(b)
 j=json.loads(b) if n.endswith('.json') else None
 contexts.append(dict(path=str(p),sha256=sha(b),bytes=len(b),keys=list(j) if isinstance(j,dict) else None,role='mutable context, excluded from scientific freeze' if n=='NEXT.md' else 'campaign context'))
j=json.loads((L/'history-receipt.json').read_bytes());records=[];omitted=[];target=re.compile(r'2606[.]25250|375559|McDermott|Stable quadratic polynomials over',re.I);hits=[];refreshed=[]
for p,h,z in j['records']:
 if any(v in p for v in ['/tamper-controls/','/candidate-copy/','/root-two-candidate-checks-r1/']):omitted.append(dict(path=p,role='generated validation/candidate copy'));continue
 b=(R/p).read_bytes();nh=sha(b)
 if nh!=h:refreshed.append(p)
 records.append([p,nh,len(b)])
 if target.search(b.decode(errors='replace')):hits.append(p)
save('history-final.json',dict(baseline='history-receipt.json',records=records,omitted_generated_roles=omitted,changed_since_initial=refreshed,target_pattern=target.pattern,target_hits=hits,cutoff=None,original_r111_r113=[p for p,h,z in records if re.search(r'sol-fresh-source-discovery-r11[123]/',p)]))
assert not hits
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
for h in http:
 if 'sha256' in h:assert sha((L/'sources'/h['name']).read_bytes())==h['sha256']
save('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),local_research_date='2026-10-29 America/Los_Angeles',result='zero; Conjecture1.5 unresolved',contexts=contexts,http=http,history=dict(initial='history-receipt.json',final='history-final.json',alias_queries='alias-queries.jsonl',full_body=True,global_cutoff=None,limits='qualified retained original roles, not proof of whole-workspace semantic completeness'),registries=dict(receipt='registry-screen.json',omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',gaps=['aa026->a19a capped300','a19a->490f capped300','path matches do not establish semantic coverage','no whole registry clearance']),primary_scope=dict(source='2606.25250v3',latest_arxiv_date='2026-09-21',target='Conjecture1.5',published_version='No separate journal reference established; NYJM2020 predecessor actual published PDF read',companions=['2024 dissertation','NYJM26(2020)526-561']),public_counterpart=dict(url='https://mathdb.com/p/375559/non-square-conjecture-for-the-gaussian-integer-recurrence-fa',scope='unconditional Conjecture1.7 ONLY',body_read=True,chronology='observed complete solution before sustained math; displayed Posted2monthsago and August2026 summary, exact initial timestamp not established'),guard=dict(path=str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),sha256=sha((L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py').read_bytes()),AS_bytes=512*1024**2,groupRSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,qualification='RSS is sampled, not continuous; caps unchanged',env=['OPENBLAS_NUM_THREADS=1','OMP_NUM_THREADS=1','PYTHONDONTWRITEBYTECODE=1']),failures=['read.log: missing optional bs4; successful stdlib parser retry in read-retry.log'],scientific_exclusions=['context-NEXT.md','derived manifests and verification outputs'],credit=0,counts_unchanged='9 additional /39 total; next40'))
excluded={'finalmanifest.json','scientific-freeze.json','manifest-verification.json'}
allfiles=[p for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
def entry(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(L)),sha256=sha(b),bytes=len(b))
save('scientific-freeze.json',dict(entries=[entry(p) for p in allfiles if p.name!='context-NEXT.md'],exclusions=['context-NEXT.md']+sorted(excluded),scope='scientific/context/evidence bytes fixed at finalization; mutable NEXT excluded'))
allfiles.append(L/'scientific-freeze.json')
save('finalmanifest.json',dict(entries=[entry(p) for p in allfiles],exclusions=['finalmanifest.json','manifest-verification.json']))
print('freeze and manifest written',len(allfiles))
