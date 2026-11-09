from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base='frozen/lanes/sol-super-coupon-source-prior-breadth-r2/'
specs=[
 ('target-vor','https://doi.org/10.1007/s10959-025-01417-w','2025-05-28','Conjecture2.4 p6; Theorem2.5/Remark2.2 p7; Lemma3.2/Corollary3.3 and Theorem2.1 proof pp10–13; Matthews and overlap recurrence pp17–19'),
 ('target-correction','https://doi.org/10.1007/s10959-025-01432-x','2025-09-15','All three pages; dependent formulas and inconsistent introductory iid replacement'),
 ('aldous-book','https://www.stat.berkeley.edu/~aldous/RWG/book.pdf','2002; recompiled2014','Section3.5.4 pp85–87: Propositions3.22–3.23, spectral-second-moment proof through inequality deduction'),
 ('dense-cover','https://arxiv.org/pdf/1810.04772v2','2018 preprint; versioned v2','Section2 return generating functions/Lemma4; AppendixA generating-function proof and root/remainder argument')]
access=json.loads((L/base/'access.json').read_text())
coverage=[]
for name,url,date,scope in specs:
 pdf=base+'frozen-live/'+name+'.pdf';txt=base+'texts/'+name+'.txt'
 inherited=[{k:a.get(k) for k in ['url','utc','status','sha256','bytes']} for a in access if a.get('name')==name+'.pdf']
 coverage.append(dict(name=name,pdf=pdf,text=txt,sha256=sha(L/pdf),source_url=url,chronology=date,actual_body_scope=scope,inherited_retrieval=inherited))
pdf='frozen/lanes/sol-wide-analytic-source-scout-r254/primary/1202.3900v1.pdf'
coverage.append(dict(name='Keller',pdf=pdf,text=pdf.replace('/primary/','/texts/').replace('.pdf','.txt'),sha256=sha(L/pdf),source_url='https://arxiv.org/pdf/1202.3900v1',chronology='2012 versioned preprint',actual_body_scope='Section2 assumptions(1)–(6), Section3.1 equations(15)–(22), Section3.2 Proposition2 and proof, pp2–8'))
(L/'body-coverage.json').write_text(json.dumps({'bodies':coverage,'not_claimed':'Other frozen bodies are retention only; inherited summaries are not independent body coverage. No new retrieval.'},indent=2))
b=json.loads((L/'bindings.json').read_text())
proofs=[r for r in b['records'] if Path(r['original']).name in ['RENEWAL-BRIDGE.md','PROOF.md']]
(L/'provenance.json').write_text(json.dumps(dict(review_date='2026-10-30',freeze_time=b['frozen_at'],scientific_input_count=sum(not r['administrative'] for r in b['records']),administrative_snapshots_only=True,derivation_bindings=proofs,body_coverage='body-coverage.json',access_evidence=base+'access.json',prior_reviews=['frozen/lanes/sol-dependent-super-coupon-preliminary-review-r1/review.md',base+'review.md'],new_network_requests=0,guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',limits=dict(address_space_mib=512,group_rss_mib=512,cpu_seconds=210,wall_seconds=230),environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),verdict=dict(math='PASS new renewal route',substantive='recommend EXCLUDE_ROUTINE_CLASSICAL_ADAPTATION',novelty='HOLD',formal='NOT READY'),root_only_accepts_counts=True,counts=dict(additional=9,total=39,next=40)),indent=2))
files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
(L/'finalmanifest.json').write_text(json.dumps(dict(created_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),algorithm='sha256',excludes=['finalmanifest.json','verification-receipt.json'],files=files),indent=2))
print('manifest files',len(files))
