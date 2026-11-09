from pathlib import Path
import json,hashlib,shutil
L=Path(__file__).resolve().parent
shutil.copyfile('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md',L/'administrative'/'ancestor-AGENTS.md')
scopes={
 'accepted':('Accepted manuscript, title date 2021-05-30; Essex Accepted Version','definitions pp1-5; quantile mixture p7; density class p11; Conjecture1, versions(i)-(iii), Example3 pp25-26','actual primary body'),
 'robust':('arXiv2406.13539v2; revision2025-05-27; title2025-05-28','Section4.3 pp24-29, Proposition11/proof, Theorem4, Proposition12/proof','actual primary body'),
 'extremes':('arXiv2209.02039v3; title2024-03-08','Introduction; Theorem4.1 and Corollaries4.2-4.4 pp12-13; Theorem4.5 p14','actual primary statements/context; appendix proofs not fully read'),
 'systemic':('arXiv2410.00158v2; revision2025-12-16','Introduction citation; Section3.2 Theorem3.1 pp7-8 and adjacent Theorem3.2','actual primary statements/context; complete long proofs not read')}
coverage=[]
for r in map(json.loads,(L/'access.jsonl').read_text().splitlines()):
 n=r['name']; version,scope,kind=scopes.get(n,('see response','metadata, discovery or access failure only','not a primary proof body'))
 coverage.append({k:r[k] for k in ['name','url','utc','status','bytes','sha256'] if k in r}|{'version':version,'inspected_scope':scope,'authority':kind})
for name in ['sol-quantile-aggregation-preliminary-review-r1','sol-quantile-aggregation-full-r1']:
 for n in ['freeze.json','review.md','PROOF.md','provenance.md']:
  p=L.parent/name/n
  if p.exists():coverage.append({'immutable_reference':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'scope':'full review/proof or inherited source bindings and provenance, reused without copying'})
(L/'source-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
m={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'manifest_entries':len(m),'coverage_records':len(coverage)}))
