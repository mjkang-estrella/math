import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;I=P.parent/'root-mathdb-breadth-intake-r563';C=P.parent/'pi-mathdb-full-corpus-inventory-r301'
ids=set(json.loads((I/'reserved-ids.json').read_text())['ids']);out=[]
for e in json.loads((C/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   out.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line':n,'literal_statement':r['statement'],'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
out.sort(key=lambda x:x['mathdb_id']);(P/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for x in out[int(sys.argv[1]):int(sys.argv[2])]:
 print('\nID',x['mathdb_id'], 'LINE',x['corpus_line']);print(x['literal_statement']);print('SOURCE',x['record']['source_url'])
