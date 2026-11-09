exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('urls=json.loads')[0])
import re
r=json.loads((l/'results.json').read_text());reserved=json.loads((l/'reservation.json').read_text())['ids']
assert len(r)==20 and set(map(int,r))==set(reserved)
assert all(x['accepted_credit']==0 and x['pi_plan'] is None for x in r.values())
assert (l/'reservation.json').read_bytes() and hashlib.sha256((l/'reservation.json').read_bytes()).hexdigest()==(l/'reservation.sha256').read_text().split()[0]
receipts=[json.loads(f.read_text()) for f in (l/'sources').glob('*.receipt.json')]
for x in receipts:
 if x.get('status')==200:
  f=l/x['artifact'];assert f.stat().st_size==x['bytes'];assert hashlib.sha256(f.read_bytes()).hexdigest()==x['sha256']
validation={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_key_count':20,'reservation_immutable':True,'raw_newlines_preserved':True,'http_receipts_verified':len(receipts),'credit':0,'qualified_new_endpoints':0,'lean_or_solver_execution':False,'live_launched_jobs':0,'process_deviations':'Initial uncapped navigation/AGENTS-TASK read, disclosed in PROCESS-LOG.md; all subsequent research processing bounded.'}
(l/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
files=sorted(f for f in l.rglob('*') if f.is_file() and f.name!='manifest.sha256')
(l/'manifest.sha256').write_text(''.join(hashlib.sha256(f.read_bytes()).hexdigest()+'  '+str(f.relative_to(l))+'\n' for f in files))
print(json.dumps(validation));print('Manifest artifacts:',len(files))
