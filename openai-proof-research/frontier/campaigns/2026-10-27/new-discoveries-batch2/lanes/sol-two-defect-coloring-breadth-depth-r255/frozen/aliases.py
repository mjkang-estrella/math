import pathlib,hashlib,json,re
L=pathlib.Path(__file__).parent;B=L.parent.parent
out=[];hits=[]
for lane in sorted((B/'lanes').iterdir()):
 if lane==L:continue
 for name in ['SCOUTING.md','SUMMARY.md','discovery.md']:
  p=lane/name
  if not p.is_file() or p.stat().st_size>500000:continue
  data=p.read_bytes();h=hashlib.sha256(data).hexdigest();out.append({'path':str(p),'sha256':h})
  s=data.decode(errors='replace')
  if re.search(r'2101\.05229|Elphick|Wocjan|positive spectral|spectral energy',s,re.I):
   hits.append({'path':str(p),'excerpts':[s[max(0,m.start()-200):m.end()+1600] for m in list(re.finditer(r'2101\.05229|Elphick|Wocjan|positive spectral|spectral energy',s,re.I))[:6]]})
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h
(L/'history-bindings.json').write_text(json.dumps(out,indent=2));(L/'history-hits.json').write_text(json.dumps(hits,indent=2));print(json.dumps(hits,indent=2)[:17000]);print('files',len(out))
