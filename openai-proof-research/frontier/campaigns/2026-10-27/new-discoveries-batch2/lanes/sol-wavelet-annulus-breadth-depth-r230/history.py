from pathlib import Path
import hashlib,json,re
L=Path(__file__).resolve().parent
terms=['Manskova','Womersley','Matzke','Grabner','Marzo','snake polynomial','Nikolov','Hadamard','Petrunin','two-convex','optical fiber','shortcut','maximal finite subgroup','Teplitskaya','achievement set','Cantorval','Asanjarani','Nazarathy','MMPP']
rows=[];hits=[]
campaigns=L.parents[3]
lanes=[p for root in campaigns.glob('*/new-discoveries*/lanes') for p in root.iterdir()]
for lane in lanes:
 if not lane.is_dir() or lane==L:continue
 for name in ['SUMMARY.md','SCOUTING.md','discovery.md']:
  p=lane/name
  if not p.is_file() or p.stat().st_size>200000:continue
  data=p.read_bytes();h=hashlib.sha256(data).hexdigest()
  # Freeze the exact bytes in memory before decoding; immutable direct reference, no historical copies.
  s=data.decode(errors='replace');found=[]
  for t in terms:
   m=re.search(re.escape(t),s,re.I)
   if m:found.append({'term':t,'excerpt':s[max(0,m.start()-100):m.end()+250]})
  assert h==hashlib.sha256(p.read_bytes()).hexdigest()
  rows.append({'path':str(p),'sha256':h})
  if found:hits.append({'path':str(p),'hits':found})
(L/'history-references.json').write_text(json.dumps(rows,indent=2))
(L/'history-hits.json').write_text(json.dumps(hits,indent=2))
print('references',len(rows))
for t in terms:
 matches=[x for x in hits if any(y['term']==t for y in x['hits'])]
 print(t,len(matches))
 for x in matches[:4]:print(x['path'].split('/')[-2],next(y['excerpt'] for y in x['hits'] if y['term']==t))
