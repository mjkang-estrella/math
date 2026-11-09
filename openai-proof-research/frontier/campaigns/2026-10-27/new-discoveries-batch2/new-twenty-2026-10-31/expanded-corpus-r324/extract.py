R=json.loads((P/'reservation.json').read_text()); ids=set(R['ids']); assert len(ids)==20
h=hashlib.sha256((P/'reservation.json').read_bytes()).hexdigest(); expected=(P/'reservation.sha256').read_text().split()[0]; assert h==expected
(P/'reservation-before.json').write_text(json.dumps(dict(actual=h,expected=expected,match=True)))
base=P.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
(P/'literal').mkdir(exist_ok=True)
out={}
for chunk in sorted(base.glob('mathdb-normalized-chunk-*.jsonl')):
 data=chunk.read_bytes(); ch=hashlib.sha256(data).hexdigest()
 for n,line in enumerate(data.splitlines(keepends=True),1):
  record=json.loads(line); rid=record.get('id',record.get('mathdb_id'))
  if str(rid) not in {str(i) for i in ids}:continue
  rid=str(rid); (P/'literal'/f'{rid}.raw.jsonl').write_bytes(line)
  statement=record.get('statement',record.get('problem_statement',''))
  out[rid]=dict(chunk=str(chunk),line=n,chunk_sha256=ch,raw_sha256=hashlib.sha256(line).hexdigest(),statement_sha256=hashlib.sha256(statement.encode()).hexdigest(),statement_field='statement',parsed=record)
assert len(out)==20,len(out)
(P/'provenance.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for rid,v in out.items():print(rid,json.dumps(v['parsed'],ensure_ascii=False))
