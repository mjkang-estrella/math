import pathlib,hashlib,json,sys,datetime,urllib.request,urllib.parse,xml.etree.ElementTree as ET
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
if sys.argv[1]=='write':
 records=[json.loads(s) for s in (L/'provenance.jsonl').read_text().splitlines()]
 # Check every scientific original and frozen copy before constructing final metadata.
 for r in records:
  assert sha(L/r['copy'])==r['sha256'],r
  if 'original' in r and not r.get('administrative'):assert sha(pathlib.Path(r['original']))==r['sha256'],r
 ids=[pathlib.Path(r['copy']).stem for r in records if 'url' in r]
 url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'id_list':','.join(ids),'max_results':40})
 try:
  data=urllib.request.urlopen(url,timeout=35).read(3000000)
  (L/'chronology-api.xml').write_bytes(data)
  ns={'a':'http://www.w3.org/2005/Atom'}
  rows=[]
  for e in ET.fromstring(data).findall('a:entry',ns):
   rows.append({k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']})
  (L/'chronology.json').write_text(json.dumps({'url':url,'retrieved_at':now(),'sha256':hashlib.sha256(data).hexdigest(),'entries':rows},indent=2)+'\n')
 except Exception as e:
  (L/'chronology.json').write_text(json.dumps({'url':url,'error':str(e),'retrieved_at':now()},indent=2)+'\n')
 sources=[]
 for r in records:
  r=dict(r)
  if r['copy'].endswith('.pdf'):
   q=(L/r['copy']).with_suffix('.txt');r['extraction']={'path':str(q.relative_to(L)),'sha256':sha(q)}
  sources.append(r)
 (L/'provenance.json').write_text(json.dumps({'date':now(),'records':sources,'registry_status':'Current full heads unavailable; denied routes not retried','scientific_freeze':'local original/copy SHA256 before scientific reads; downloaded bytes fixed before extraction; before/after verification','administrative':'snapshots only','history':'hash-bound immutable references without recursive copies;819 reports; bounded aliases only'},indent=2)+'\n')
 excluded={'manifest.json','verification-receipt.json'}
 files=[{'path':str(p.relative_to(L)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
 (L/'manifest.json').write_text(json.dumps({'created':now(),'excludes':sorted(excluded),'files':files},indent=2)+'\n')
 print('MANIFEST WRITTEN',len(files),'files; requires separate guarded verify')
elif sys.argv[1]=='verify':
 manifest=json.loads((L/'manifest.json').read_text());errors=[]
 for r in manifest['files']:
  p=L/r['path']
  if not p.exists() or sha(p)!=r['sha256']:errors.append(r['path'])
 refs=json.loads((L/'provenance.json').read_text())['records'];originals=0
 for r in refs:
  if sha(L/r['copy'])!=r['sha256']:errors.append(r['copy'])
  if 'original' in r and not r.get('administrative'):
   originals+=1
   if sha(pathlib.Path(r['original']))!=r['sha256']:errors.append('original '+r['original'])
 history=json.loads((L/'history-references.json').read_text());hist_errors=[]
 for r in history:
  if sha(pathlib.Path(r['path']))!=r['sha256']:hist_errors.append(r['path'])
 expected={r['path'] for r in manifest['files']}
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in manifest['excludes']}
 if expected!=actual:errors.append('inventory mismatch')
 receipt={'verified_at':now(),'pass':not errors and not hist_errors,'manifest_sha256':sha(L/'manifest.json'),'files_verified':len(expected),'scientific_originals_verified':originals,'history_references_verified':len(history),'errors':errors,'changed_history':hist_errors,'administrative_originals':'not live-immutability checked; snapshots only','limits':'mandated helper guard;512MiB AS/group RSS CPU210 wall230; no raises'}
 (L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
 assert receipt['pass']
