import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];ids=json.loads((D/'reservation.json').read_text())['ids'];rows=[]
for l in (D/'history-matches.txt').read_text().splitlines():
 for i in ids:
  m=re.search(r'(?<!\d)'+str(i)+r'(?!\d)',l)
  if m:rows.append({'id':i,'location':l.split(':',2)[:2],'context':l[max(0,m.start()-120):m.end()+240]})
(D/'history-digest.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
