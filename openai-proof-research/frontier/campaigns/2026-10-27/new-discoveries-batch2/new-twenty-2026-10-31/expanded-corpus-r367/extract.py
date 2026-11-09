b=(L/'reservation.json').read_bytes(); assert sha(b)=='73de0ea98d4dae8f1548b4802fe99c2b5a39bd7ad3f1b971f8dbcdb363682a6e'
r=json.loads(b); ids=set(r['ids']); assert len(ids)==20
save('reservation-before.json',{'sha256':sha(b),'sidecar':(L/'reservation.sha256').read_text(),'ids':r['ids']})
root=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
found={}
for p in sorted(root.glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes(); chunksha=sha(data)
 for lineno,raw in enumerate(data.splitlines(keepends=True),1):
  obj=json.loads(raw); ident=obj.get('mathdb_id',obj.get('id'))
  if ident is not None: ident=int(ident)
  if ident not in ids: continue
  assert ident not in found
  statement=obj.get('statement',obj.get('problem_statement',''))
  found[ident]={'id':ident,'chunk':str(p),'chunk_sha256':chunksha,'one_based_line':lineno,'raw_sha256':sha(raw),'raw_base64':base64.b64encode(raw).decode(),'newline':raw.endswith(b'\n'),'statement_sha256':sha(statement.encode()),'full_parsed_json':obj}
assert set(found)==ids
save('raw-provenance.json',found)
for ident in r['ids']:
 o=found[ident]['full_parsed_json']; print('RECORD',ident,json.dumps(o,ensure_ascii=False))
allow=json.loads((L/'historical-results-allowlist.json').read_text()); print('ALLOWTYPE',type(allow).__name__)
paths=allow if isinstance(allow,list) else allow.get('paths',[])
h=[];hits=[]
for x in paths:
 if any(t in x.lower() for t in ['crown','transitive-bunkbed','tournament']):continue
 p=pathlib.Path(x); data=p.read_bytes();h.append({'path':x,'sha256':sha(data)})
 o=json.loads(data)
 text=json.dumps(o,ensure_ascii=False)
 if any(str(i) in text for i in ids):hits.append({'path':x,'result':o})
save('historical-read-inventory.json',h);save('historical-hits.json',hits)
print('HISTORICAL',len(h),'hits',json.dumps(hits,ensure_ascii=False))
