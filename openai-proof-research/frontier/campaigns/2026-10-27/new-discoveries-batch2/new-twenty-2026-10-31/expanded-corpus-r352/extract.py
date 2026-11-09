R=json.loads(read(P/"reservation.json")); ids=set(R["ids"]);out={}
corpus=P.parent.parent/"lanes/pi-mathdb-full-corpus-inventory-r301/corpus"
for p in sorted(corpus.glob("mathdb-normalized-chunk-*.jsonl")):
 b=read(p)
 for i,line in enumerate(b.splitlines(keepends=True),1):
  row=json.loads(line);id=row.get("mathdb_id",row.get("id"))
  if id in ids:
   assert line.endswith(b"\n");put("literal/"+str(id)+".jsonl",line);js("literal/"+str(id)+".json",row)
   stmt=row.get("statement",row.get("statement_text",""));stmt=stmt if isinstance(stmt,str) else json.dumps(stmt,ensure_ascii=False)
   out[str(id)]={"chunk":str(p),"one_based_line":i,"chunk_sha256":hashlib.sha256(b).hexdigest(),"raw_sha256":hashlib.sha256(line).hexdigest(),"statement_sha256":hashlib.sha256(stmt.encode()).hexdigest(),"record":row}
 assert len(out)<=20
assert len(out)==20
js("provenance.json",out)
for k,v in out.items():print(k,json.dumps(v["record"],ensure_ascii=False))
