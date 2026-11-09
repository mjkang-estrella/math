import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent; f=json.loads((L/'input-bindings.json').read_text());ids=set(f['reserved_ids']); found=[]
for e in f['references']:
 if '/corpus/mathdb-normalized-chunk-' not in e['path']:continue
 p=pathlib.Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 for line in b.splitlines():
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   r['corpus_path']=str(p);r['statement_sha256']=hashlib.sha256(r['statement'].encode()).hexdigest();found.append(r)
assert len(found)==50
found.sort(key=lambda r:f['reserved_ids'].index(r['mathdb_id']))
(L/'statements.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
for r in found:print('\nID',r['mathdb_id'],r['title'],'\nSOURCE',r['source_url'],'\n'+r['statement'])
