from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];mf=json.loads((L/'finalmanifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in mf['excludes']}
if actual!=set(mf['files']):errors.append('manifest coverage')
for name,h in mf['files'].items():
 if sha(L/name)!=h:errors.append('manifest '+name)
for r in json.loads((L/'freeze.json').read_text()):
 for k in ['original','copy']:
  if sha(Path(r[k]))!=r['sha256']:errors.append('freeze '+k+' '+r[k])
for r in [json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]:
 if 'sha256' not in r:continue
 p=Path(r['path'])
 if not p.is_absolute():p=Path.cwd()/p
 if sha(p)!=r['sha256']:errors.append('primary '+str(p))
 if 'text_sha256' in r and sha(p.with_suffix('.txt'))!=r['text_sha256']:errors.append('text '+str(p))
hist=json.loads((L/'frozen/history-index.json').read_text())['records']
for r in hist:
 if sha(Path(r['snapshot_reference']))!=r['sha256']:errors.append('history '+r['original'])
c=json.loads((L/'checks.json').read_text())
assert c['matrix_exponents'][0]['zero_counts']==[5,4,2,1,0]
assert all(x['exponent']==(x['n']-1)**2+1 for x in c['matrix_exponents'])
assert len(c['support_families'])==4
receipt={'utc':str(datetime.datetime.now(datetime.timezone.utc)),'status':'PASS' if not errors else 'FAIL','errors':errors,'manifest_sha256':sha(L/'finalmanifest.json'),'verified_files':len(mf['files']),'verified_history_references':len(hist),'verified_frozen_bindings':len(json.loads((L/'freeze.json').read_text())),'checks':'exact saved integers and support-family counts; universal proofs require human review','limits':'512MiB AS/groupRSS; CPU210; wall230; distinct supplied-guard invocation','count_credit':0}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
raise SystemExit(bool(errors))
