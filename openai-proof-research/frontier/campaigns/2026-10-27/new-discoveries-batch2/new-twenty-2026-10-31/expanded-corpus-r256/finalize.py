import pathlib,json,hashlib,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
L=pathlib.Path(__file__).resolve().parent
for name in ['SUMMARY.md','SOURCE-REVIEW.md']:
 p=L/name;s=p.read_text()
 for a,b in {'remains52/60 beyond39':'remains 52/60 beyond 39','Theorem7.2/Corollary7.3':'Theorem 7.2/Corollary 7.3','Yu\'s2018':'Yu\'s 2018','the2023':'the 2023','rate-limit403':'rate-limit 403','Omega6225930':'Omega 6225930','IDs328314/328558/328770':'IDs 328314/328558/328770','Conjecture4.8':'Conjecture 4.8','at20:34UTC':'at 20:34 UTC','affinity0,1':'affinity 0,1'}.items():s=s.replace(a,b)
 p.write_text(s)
# Receipts collected, not copied into claims of complete literature clearance.
receipts=[json.loads(p.read_text()) for p in sorted(L.glob('*.receipt.json'))]
(L/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
R=json.loads((L/'results.json').read_text());reservation=json.loads((L/'reservation.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest()
assert set(R)=={str(i) for i in reservation['ids']} and len(R)==20
for k,d in R.items():
 raw=(L/(k+'.raw.jsonl')).read_bytes();assert raw.endswith(b'\n') and h(raw)==d['provenance']['raw_sha256'];assert json.loads(raw)==d['record'];assert h(d['literal_statement'].encode())==d['provenance']['statement_sha256'];assert d['credit']==0
report={'results':20,'literal_raw_statement_integrity':'PASS','reservation_disjoint':'PASS as reservation-validation.json','no_lean_or_solver':'No execution performed','all_credit':0,'campaign_count_unchanged':'52/60','rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'known_limits':['HEAD refresh403','incomplete current citing/erratum/journal/figure clearance','no new full endpoint']}
(L/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
manifest={p.name:h(p.read_bytes()) for p in L.iterdir() if p.is_file() and p.name not in ['HASHES.json','SHA256SUMS']};(L/'HASHES.json').write_text(json.dumps(manifest,indent=2)+'\n');(L/'SHA256SUMS').write_text(''.join(f'{v}  {k}\n' for k,v in sorted(manifest.items())));print(json.dumps(report))
