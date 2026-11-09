import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parent.parent
rows=json.loads((D/'extracted.json').read_text()); ids=set(rows)
out=[]
for p in B.rglob('*'):
 if not p.is_file() or D in p.parents or p.suffix not in ('.md','.json'):continue
 if not (p.suffix=='.md' or any(w in p.name for w in ['results','ledger','review','context'])):continue
 if p.stat().st_size>2000000:continue
 try:txt=p.read_text()
 except:continue
 for n,l in enumerate(txt.splitlines(),1):
  if len(l)>2500:continue
  match=[i for i in ids if re.search(r'(?<![\da-f])'+i+r'(?![\da-f])',l) or rows[i]['title'].lower() in l.lower()]
  if match:out.append({'path':str(p),'line':n,'ids':match,'text':l})
(D/'outputs/history-filtered.json').write_text(json.dumps(out,indent=2))
for p in [B/'ledger.json',B/'prior-campaign-context.json',D.parent/'ledger.json']:
 o=json.loads(p.read_text()); print(str(p),hashlib.sha256(p.read_bytes()).hexdigest());print(json.dumps({k:v for k,v in o.items() if k not in ['reservations','coverage','reviewed','lane_assignments']},ensure_ascii=False)[:90000])
print('HISTORY',json.dumps(out,indent=2))
