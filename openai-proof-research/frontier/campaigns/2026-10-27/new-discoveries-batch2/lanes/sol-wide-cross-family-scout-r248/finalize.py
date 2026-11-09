import pathlib,hashlib,json,sys,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if sys.argv[1]=='write':
 records=[json.loads(s) for s in (L/'provenance.jsonl').read_text().splitlines()]
 for r in records:
  assert sha(L/r['copy'])==r['sha256'],r
 # Preserve distinct copies of all primary blobs before the final verification.
 for p in sorted((L/'sources').glob('*.pdf')):
  if p.name[0:12].isalnum() and '-' in p.name:continue
  h=sha(p);q=p.with_name(h[:12]+'-'+p.name)
  if not q.exists():q.write_bytes(p.read_bytes())
  assert sha(p)==sha(q)==h
  if not any(r.get('original')==str(p) for r in records):records.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,administrative=False,late_dual_copy=True))
 refs=json.loads((L/'history-references.json').read_text())
 out=dict(lane=L.name,counts=dict(additional=9,total=39,next=40),discovery_credit=0,root_alone_accepts=True,resource_limits=dict(AS_bytes=512*1024**2,group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230),records=records,history_reference_count=len(refs),limitations='FAILURES.md',verified_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
 (L/'provenance.json').write_text(json.dumps(out,indent=2))
 manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
 (L/'manifest.json').write_text(json.dumps(manifest,indent=2));print('manifest files',len(manifest))
if sys.argv[1]=='verify':
 manifest=json.loads((L/'manifest.json').read_text());bad=[n for n,h in manifest.items() if sha(L/n)!=h]
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
 assert set(manifest)==actual and not bad,(bad,actual-set(manifest))
 pv=json.loads((L/'provenance.json').read_text());verified=0;external_changes=[]
 for r in pv['records']:
  assert sha(L/r['copy'])==r['sha256']
  if r.get('original') and not r.get('administrative'):
   if sha(pathlib.Path(r['original']))!=r['sha256']:external_changes.append(r['original'])
   verified+=1
 assert not external_changes,external_changes
 out=dict(pass_verification=True,manifest_sha256=sha(L/'manifest.json'),files=len(manifest),scientific_original_copy_records_verified=verified,administrative_snapshots_only=True,excludes=['manifest.json','verification-receipt.json'],time=datetime.datetime.now(datetime.timezone.utc).isoformat())
 (L/'verification-receipt.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
