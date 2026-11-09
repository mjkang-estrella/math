import pathlib,json,hashlib,resource,datetime,urllib.request,urllib.error,subprocess
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent; B=L.parent; C=B.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
h=lambda b:hashlib.sha256(b).hexdigest()
ids=json.loads((L/'reservation.json').read_text())['ids']
if __name__=='__main__':
 rows={}
 for p in sorted(C.glob('mathdb-normalized-chunk-*.jsonl')):
  for i,raw in enumerate(p.open('rb'),1):
   d=json.loads(raw)
   if d['mathdb_id'] in ids:
    k=str(d['mathdb_id']); (L/f'{k}.raw.jsonl').write_bytes(raw);(L/f'{k}.statement.txt').write_text(d['statement'])
    rows[k]={'record':d,'provenance':{'chunk':str(p),'line_one_based':i,'raw_sha256':h(raw),'statement_sha256':h(d['statement'].encode()),'raw_includes_newline':raw.endswith(b'\n')}}
 (L/'literal-records.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
 for k,d in rows.items():print(k,d['record']['title'],'\n',d['record']['statement'],'\nSOURCE',d['record']['source_url'],'\n')
