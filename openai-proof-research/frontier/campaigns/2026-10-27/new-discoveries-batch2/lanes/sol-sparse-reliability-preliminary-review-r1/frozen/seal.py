from pathlib import Path
import json,hashlib,datetime,sys
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
def verify_pairs(rows):
 for r in rows:
  assert sha(Path(r['original']).read_bytes())==r['sha256'],r['original']
  assert sha((L/r['copy']).read_bytes())==r['sha256'],r['copy']
 return len(rows)
if sys.argv[1]=='primary-freeze':
 pairs=json.loads((L/'scientific-input-freeze.json').read_text());verify_pairs(pairs)
 for p in sorted((L/'sources').iterdir()):
  q=L/'source-working-copies'/p.name;q.parent.mkdir(exist_ok=True);b=p.read_bytes();h=sha(b);q.write_bytes(b)
  pairs.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
 old=L.parent/'sol-fresh-source-discovery-r193'
 for n in ['co.html','dm.html']:
  p=old/'sources'/n;q=L/'context'/('r193-'+n);b=p.read_bytes();q.write_bytes(b)
  pairs.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=sha(b)))
 save('scientific-input-freeze.json',pairs);print(verify_pairs(pairs))
elif sys.argv[1]=='seal':
 pairs=json.loads((L/'scientific-input-freeze.json').read_text());n=verify_pairs(pairs)
 save('scientific-verification.json',dict(utc=now(),status='PASS',original_copy_pairs=n,administrative_snapshots_not_live_bound=True))
 save('scientific-freeze.json',dict(utc=now(),pairs=pairs,excludes=['snapshot-NEXT.md','snapshot-ledger.json','snapshot-prior-campaign-context.json'],note='Administrative files preserved as snapshots only; primary retrieval hashes in http.jsonl authenticate first bytes.'))
 excluded={'finalmanifest.json','manifest-verification.json'}
 entries={str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded}
 save('finalmanifest.json',dict(utc=now(),excluded=sorted(excluded),files=entries));print(dict(pairs=n,manifest_files=len(entries)))
elif sys.argv[1]=='verify':
 m=json.loads((L/'finalmanifest.json').read_text());seen={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in m['excluded']};assert seen==set(m['files'])
 for n,h in m['files'].items():assert sha((L/n).read_bytes())==h,n
 count=verify_pairs(json.loads((L/'scientific-input-freeze.json').read_text()))
 save('manifest-verification.json',dict(utc=now(),status='PASS',manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),files=len(seen),original_copy_pairs=count,exclusions=m['excluded'],separate_guarded_invocation=True));print(dict(status='PASS',files=len(seen),pairs=count))
