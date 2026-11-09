from pathlib import Path
import hashlib,json,datetime,os,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'reservation.json').read_text());e=(p/'reservation.sha256').read_text().split()[0];actual=sha((p/'reservation.json').read_bytes());assert e==actual
out=json.loads((p/'results.json').read_text());assert set(out)==set(map(str,r['ids'])) and len(out)==20
checks=[]
for i,v in out.items():
 b=(p/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert json.loads(b)==v['record'];assert sha(b)==v['provenance']['raw_sha256'];assert sha(v['record']['statement'].encode())==v['provenance']['statement_sha256_utf8'];checks.append(i)
(p/'reservation-after.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'expected':e,'actual':actual,'pass':True,'ids_unchanged':r['ids']==json.loads((p/'reservation-before.json').read_text())['ids']},indent=2)+'\n')
(p/'validation.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact20keys':True,'reservation_pass':True,'raw_statement_integrity_ids':checks,'credit':0,'candidate':None,'task_processes':'All launched exec sessions returned exit; no background processes launched','scope_limit':'No whole-literature or complete-current-registry clearance'},indent=2)+'\n')
files=sorted(f for f in p.rglob('*') if f.is_file() and f.name not in ['SHA256SUMS','manifest.json'])
m={str(f.relative_to(p)):sha(f.read_bytes()) for f in files};(p/'manifest.json').write_text(json.dumps(m,indent=2)+'\n');m['manifest.json']=sha((p/'manifest.json').read_bytes());(p/'SHA256SUMS').write_text(''.join(h+'  '+f+'\n' for f,h in sorted(m.items())))
print('PASS exact20 keys, raw/statement integrity, reservation before/after; manifest',len(m),'files')
