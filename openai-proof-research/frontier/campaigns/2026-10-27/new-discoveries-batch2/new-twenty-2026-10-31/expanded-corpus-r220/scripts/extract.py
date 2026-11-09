import json,hashlib,pathlib
L=pathlib.Path(__file__).resolve().parents[1]; C=L.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
ids=set(json.loads((L/'reservation.json').read_text())['ids']); out={}
for p in sorted(C.glob('*.jsonl')):
 data=p.read_bytes(); ch=hashlib.sha256(data).hexdigest()
 for i,line in enumerate(data.splitlines(keepends=True),1):
  r=json.loads(line)
  if r.get('mathdb_id') in ids:
   k=str(r['mathdb_id']); (L/'raw'/f'{k}.jsonl').write_bytes(line)
   out[k]={'chunk':str(p),'line':i,'chunk_sha256':ch,'raw_sha256':hashlib.sha256(line).hexdigest(),'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'record':r}
(L/'outputs/provenance.json').write_text(json.dumps(out,indent=2))
(L/'outputs/statements.txt').write_text('\n\n'.join(k+' '+v['record']['title']+'\n'+v['record']['statement']+'\nSOURCE '+str(v['record'].get('source_name')) for k,v in out.items()))
print((L/'outputs/statements.txt').read_text())
