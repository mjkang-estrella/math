import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def h(b): return hashlib.sha256(b).hexdigest()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
(L/'frozen').mkdir(exist_ok=True)
rows=[];seen={}
for name in ['root-clique-corona-preliminary-adoption-r1','root-r168-preliminary-freeze-r1']:
 p=L.parent/name/'review-freeze.json'
 obj=json.loads(p.read_bytes())
 for e in obj['files']:
  s=pathlib.Path(e['path']); b=s.read_bytes(); digest=h(b)
  assert len(b)==e['bytes'] and digest==e['sha256'],str(s)
  if digest not in seen:
   c=L/'frozen'/(digest+'-'+s.name);c.write_bytes(b);seen[digest]=str(c)
  rows.append(dict(e,copy=seen[digest],verified_utc=now()))
(L/'before-freeze.json').write_text(json.dumps({'utc':now(),'files':rows,'unique_copies':len(seen)},indent=2)+'\n')
for name in ['ledger.json','prior-campaign-context.json','NEXT.md']:
 p=B/name;b=p.read_bytes(); txt=b.decode(); print(name,len(b),h(b));
 if name.endswith('.json'):
  o=json.loads(txt);print('keys',list(o)[:30]);print(txt[:1800])
 else:
  lines=txt.splitlines(); matches=[(i+1,x) for i,x in enumerate(lines) if any(k in x.lower() for k in ['r168','clique','corona','9/30','39/60'])];print(matches[-18:])
print('frozen',len(rows),'unique',len(seen))
