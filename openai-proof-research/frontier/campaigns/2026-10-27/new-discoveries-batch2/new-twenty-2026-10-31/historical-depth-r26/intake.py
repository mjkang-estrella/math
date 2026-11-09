import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parent; B=D.parent.parent
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'reservation.json').read_text()); receipts=[]
for group in ['prior_report_hashes','input_hashes']:
 for p,want in r[group].items():
  got=h(pathlib.Path(p).read_bytes());receipts.append(dict(path=p,expected=want,actual=got,match=want==got,group=group))
  if group=='prior_report_hashes': assert want==got
old={}
for p in r['prior_report_hashes']:
 for x in json.load(open(p)):
  if x['mathdb_id'] in r['ids']: old[str(x['mathdb_id'])]=x
(D/'inherited-exact-entries.json').write_text(json.dumps(old,indent=2))
notes=[]
for p in r['prior_report_hashes']:
 for n in ['SUMMARY.md','SOURCE-READING.md','source-reading.md','FAILURES.md','CHECKS.md']:
  q=pathlib.Path(p).parent/n
  if q.exists(): notes.append('FILE '+str(q)+' SHA256 '+h(q.read_bytes())+'\n'+q.read_text())
(D/'inherited-notes.txt').write_text('\n\n'.join(notes))
raw={}; (D/'raw').mkdir(exist_ok=True)
for p in (B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl'):
 content=p.read_bytes()
 for i,line in enumerate(content.splitlines(keepends=True),1):
  x=json.loads(line);id=str(x.get('mathdb_id',x.get('id')))
  if id in old:
   (D/'raw'/f'{id}.jsonl').write_bytes(line)
   raw[id]=dict(path=str(p),line_1based=i,chunk_sha256=h(content),raw_line_sha256=h(line),raw_line_bytes=len(line),record=x)
assert len(raw)==40,len(raw)
(D/'raw-bindings.json').write_text(json.dumps(raw,indent=2));(D/'binding-verification.json').write_text(json.dumps(receipts,indent=2))
print('Verified/extracted',len(raw),'records; report hashes',all(x['match'] for x in receipts if x['group']=='prior_report_hashes'));print(json.dumps(receipts,indent=2))
