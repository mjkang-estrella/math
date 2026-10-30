from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
HERE=Path(__file__).resolve().parent
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for number in [185,186,187]:
 P=HERE.parent/f'root-r{number}-handback';P.mkdir(exist_ok=True)
 S=P.parent/f'sol-fresh-source-discovery-r{number}';R=S.parents[5]
 freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
 (P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
 counts={}
 for name in ['scientific-freeze.json','finalmanifest.json']:
  j=json.loads((S/name).read_text());raw=j.get('records',j.get('files'))
  if isinstance(raw,dict):rows=[(n,v['sha256'],v['bytes']) for n,v in raw.items()]
  else:rows=[(v['path'],v['sha256'],v['bytes']) if isinstance(v,dict) else tuple(v) for v in raw]
  for n,h,z in rows:assert sha(S/n)==h and (S/n).stat().st_size==z,n
  if 'exclusions' in j:assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(j['exclusions'])=={v[0] for v in rows},name
  counts[name]=len(rows)
 if number==186:
  rows=json.loads((S/'original-copy-provenance.json').read_text())['records']
  for v in rows:assert sha(S/v['copy'])==sha(R/v['original'])==v['sha256'],v
  counts['external_originals_and_copies']=len(rows)
  g=json.loads((S/'guard-binding.json').read_text());assert sha(Path(g['path']))==g['sha256']
 else:
  rows=json.loads((S/'history-receipt.json').read_text())['records']
  for n,h,z in rows:assert sha(R/n)==h and (R/n).stat().st_size==z,n
  counts['external_originals']=len(rows)
 for script in (['checks.py','power_checks.py'] if number==185 else ['checks.py']):
  shutil.copyfile(S/script,P/script)
  with (P/(script+'.log')).open('w') as f:subprocess.run([sys.executable,str(P/script)],stdout=f,stderr=subprocess.STDOUT,check=True)
  output=script.replace('.py','.json').replace('power_checks','power-checks')
  a=json.loads((P/output).read_text());b=json.loads((S/output).read_text())
  a.pop('utc',None);b.pop('utc',None);assert a==b,output
 for v in freeze:
  p=Path(v['path']);assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes']
 receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=counts,frozen_files=len(freeze),private_replay='Exact JSON equality except run UTC; originals unchanged',qualification='Diagnostics and integrity only; no independent universal proof or eligibility acceptance.')
 (P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(number,json.dumps(receipt),flush=True)
