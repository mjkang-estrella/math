import json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
if sys.argv[1]=='freeze':
 hist=json.loads((L/'history-receipt.json').read_text()); originals=[[str(R/p),h,z] for p,h,z in hist['records']]
 guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 originals.append([str(guard),sha(guard),guard.stat().st_size])
 for p,h in hist['bases']:originals.append([p,h,Path(p).stat().st_size])
 local=[[str(p.relative_to(L)),sha(p),p.stat().st_size] for p in sorted((L/'sources').iterdir()) if p.is_file()]
 save('primary-hashes.json',dict(utc=now(),records=local,access_receipts='http.jsonl'))
 save('scientific-freeze.json',dict(utc=now(),local=local,originals=originals,
  exclusions=['Self scientific-freeze.json and verification receipts are not scientific inputs.','Mutable live NEXT/ledger/prior-context are administrative only; only archived context bytes enter final manifest.'],
  qualification='Historical original scientific records and conservative copies remain individually bound. No deduplication.'))
 http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
 save('provenance.json',dict(utc=now(),status='HONEST_ZERO_PUBLICLY_RESOLVED',discovery_credit=0,counts=dict(additional=9,total=39,next=40),
  source_receipts=http,scientific_freeze='scientific-freeze.json',history=dict(records=len(hist['records']),changed=len(hist['changed']),missing=hist['missing'],bases=hist['bases']),
  chronology=[['2407.02359v2','2025-02-06','Poisson transport Remark1.6'],['2607.10769v2','2026-09-01','Poincare full theorem and explicit stronger-claim refutation'],['2609.23994v1','2026-09-21 arXiv margin; cover September22','Public Poisson refutation Example4.24'],['2609.39252v1','2026-09-30','Stronger Talagrand proof']],
  exact_source_limits=['Original Aishwarya-Rotem journal question unread; question attribution via two actual primary companions only.','Latest primary versions checked from live abs; journal metadata is not journal-body equivalence.','Current registry heads and capped historical intervals PARKED; eleven cached path screens only.','Bing reconnaissance irrelevant; no novelty inference.'],
  body_reads=['Poisson Definition1.1, Theorem1.5, Remark1.6 pp2-4','Chen-Wang Theorem4.22 and proof, Example4.24 pp39-40','Han-Zhu Theorem1.1, Remarks1.2-1.3, source comparison pp3-5, coupled Bochner sections selected; AppendixA pp32-34','Gozlan et al. Theorem2.1/Lemma2.2 actual proof pp4-6; Theorem3.2/Corollary3.3; Theorem4.1 proof; Corollary5.2'],
  guard=dict(path=str(guard),sha256=sha(guard),AS_bytes=512*1024*1024,sampled_group_RSS_bytes=512*1024*1024,CPU_seconds=210,wall_seconds=230,unchanged=True),
  checks=dict(script='checks.py',result='checks.json',status='PASS',guard_exit=0,sampled_peak_group_rss=52764672,wall_seconds=0.28108398790936917),
  forbidden_actions_performed=False,failures='failures.json plus http.jsonl',no_proof_md_reason='No full new candidate survives public-proof/refutation screen.'))
 print('scientific local',len(local),'original records',len(originals))
elif sys.argv[1]=='manifest':
 exclusions=['finalmanifest.json','manifest-verification.json']
 records=[[str(p.relative_to(L)),sha(p),p.stat().st_size] for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in exclusions]
 save('finalmanifest.json',dict(utc=now(),records=records,exclusions=exclusions,reason='Manifest self and final receipt excluded to avoid recursive hashing; scientific-verification.json is included.'))
 print('manifest records',len(records))
