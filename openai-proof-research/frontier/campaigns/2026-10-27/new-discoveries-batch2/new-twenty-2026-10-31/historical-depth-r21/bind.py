from pathlib import Path
import json,hashlib,datetime
O=Path(__file__).resolve().parent; B=O.parents[1]; R=json.loads((O/'reservation.json').read_text()); H=lambda b:hashlib.sha256(b).hexdigest()
receipts=[]
for k in ['prior_report_hashes','input_hashes']:
 for p,h in R[k].items():
  b=Path(p).read_bytes(); receipts.append(dict(path=p,expected=h,actual=H(b),match=H(b)==h,kind=k))
  if k=='prior_report_hashes': assert H(b)==h
old={}
for p in R['prior_report_hashes']:
 for x in json.loads(Path(p).read_text())['dispositions']:
  if x['mathdb_id'] in R['ids']: old[str(x['mathdb_id'])]=x
assert len(old)==40
C=B/'lanes/pi-mathdb-full-corpus-inventory-r301'; M=json.loads((C/'manifest.json').read_text()); chunks={x['path']:x for x in M['files'] if x['path'].startswith('corpus/')}
(O/'raw').mkdir(exist_ok=True); records={}; bindings={}
for path,entry in chunks.items():
 p=C/path;b=p.read_bytes();assert H(b)==entry['sha256']; assert len(b)==entry['bytes']
 receipts.append(dict(path=str(p),sha256=H(b),bytes=len(b),kind='corpus_chunk',match=True))
 for n,line in enumerate(b.splitlines(keepends=True),1):
  x=json.loads(line);i=str(x['mathdb_id'])
  if i not in old:continue
  assert x['statement']==old[i]['literal_statement'];assert H(x['statement'].encode())==old[i]['literal_statement_sha256']
  (O/'raw'/f'{i}.jsonl').write_bytes(line);records[i]=x;bindings[i]=dict(chunk=str(p),chunk_sha256=H(b),line_one_based=n,raw_sha256=H(line),statement_sha256=H(x['statement'].encode()),bytes=len(line),newline_preserved=True)
assert len(records)==40
for name,d in [('input-verification.json',receipts),('old-dispositions.json',old),('records.json',records),('raw-bindings.json',bindings)]: (O/name).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'40_exact_records':len(records),'prior_reports_verified':2,'corpus_chunks_verified':len(chunks),'input_mismatches':[x for x in receipts if not x['match']]},indent=2))
