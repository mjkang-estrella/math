import json,pathlib,hashlib,datetime
P=pathlib.Path(__file__).resolve().parents[1];B=P.parents[1];C=B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
h=lambda x:hashlib.sha256(x).hexdigest()
ids=set(json.loads((P/'reservation.json').read_text())['ids']);out={}
for f in sorted(C.glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes();ch=h(data)
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line);i=d['mathdb_id']
  if i not in ids:continue
  (P/'raw'/f'{i}.jsonl').write_bytes(line)
  out[str(i)]={'record':d,'provenance':{'chunk':str(f),'one_based_line':n,'chunk_sha256':ch,'raw_line_sha256':h(line),'statement_utf8_sha256':h(d['statement'].encode()),'raw_line_includes_newline':line.endswith(b'\n')}}
assert len(out)==40
(P/'outputs/extracted.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for i,d in out.items():
 r=d['record'];print('\nID',i,r['title'],'\n',r['statement'],'\nSOURCE',r['source_name'],r['source_url'])
ctx=[]
for f in [B/'ledger.json',B/'prior-campaign-context.json',P.parent/'ledger.json']:
 d=json.loads(f.read_text());ctx.append({'path':str(f),'sha256':h(f.read_bytes()),'accepted':d.get('accepted'),'excluded':d.get('excluded'),'candidates':d.get('candidates'),'held_candidates':d.get('held_candidates')})
(P/'outputs/inherited-context.json').write_text(json.dumps(ctx,indent=2,ensure_ascii=False)+'\n')
