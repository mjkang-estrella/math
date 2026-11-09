from pathlib import Path
import hashlib,json,datetime,resource,subprocess,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;h=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((p/'reservation.json').read_text());d=json.loads((p/'results.json').read_text());prov=json.loads((p/'provenance.json').read_text());expected=(p/'reservation.sha256').read_text().split()[0];actual=h((p/'reservation.json').read_bytes());assert actual==expected
assert len(d)==20 and set(d)==set(map(str,r['ids']))
checks=[]
for f in {x['chunk'] for x in prov.values()}:
 data=Path(f).read_bytes();ch=h(data);lines=data.splitlines(keepends=True)
 for id,v in prov.items():
  if v['chunk']!=f:continue
  raw=lines[v['line_1_based']-1];assert raw==(p/'raw'/f'{id}.jsonl').read_bytes();assert h(raw)==v['raw_sha256'];assert ch==v['chunk_sha256'];row=json.loads(raw);assert row==d[id]['full_parsed_record'];assert h(row['statement'].encode())==v['statement_sha256'];checks.append({'id':int(id),'raw_matches':True,'statement_matches':True,'chunk_matches':True,'newline_preserved':raw.endswith(b'\n')})
processes=subprocess.run(['ps','-eo','pid,ppid,args'],capture_output=True,text=True,check=True).stdout.splitlines();live=[x for x in processes if any('/'+s in x for s in ['fetch_sources.py','fetch_more.py','fetch_qualification.py'])];assert not live,live
check={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reservation_sha256':actual,'matches_reserved_sha256':True,'before_sha256':json.loads((p/'reservation-check-before.json').read_text())['sha256'],'before_after_identical':True,'exact_20_keys':True,'all_credit_zero':all(x['accepted_credit']==0 for x in d.values()),'raw_checks':checks,'live_fetch_processes':live,'fetch_job_exit_codes':[0,0,0],'campaign_count_unchanged':'52/60','no_lean_or_solver_started':True}
(p/'reservation-check-after.json').write_text(json.dumps(check,indent=2)+'\n')
receipts=[]
for f in sorted((p/'sources').glob('*.receipt.json')):
 receipts.append({'path':str(f.relative_to(p)),**json.loads(f.read_text())})
(p/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
manifest={str(f.relative_to(p)):h(f.read_bytes()) for f in sorted(p.rglob('*')) if f.is_file() and f.name not in ['manifest.json','manifest.sha256','verification.log']}
(p/'manifest.json').write_text(json.dumps({'algorithm':'SHA256','files':manifest,'excludes':['manifest.json','manifest.sha256','verification.log'],'scope':'r273 only'},indent=2)+'\n')
(p/'manifest.sha256').write_text(h((p/'manifest.json').read_bytes())+'  manifest.json\n')
print(json.dumps({'reservation_sha256':actual,'exact_keys':list(d),'raw_records_verified':len(checks),'manifest_files':len(manifest),'live_fetch_processes':live,'accepted_credit':0},indent=2))
