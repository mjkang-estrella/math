import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parents[1];R=L.parents[5];rows=json.loads((L/'extracted.json').read_text());found=[];scanned=0
for p in R.rglob('*'):
 if not p.is_file() or L in p.parents or p.name not in ['SUMMARY.md','results.json','ledger.json','prior-campaign-context.json']:continue
 try:s=p.read_text()
 except:continue
 scanned+=1
 for k,v in rows.items():
  if k in s or v['row']['title'].lower() in s.lower():
   matches=[line[:1800] for line in s.splitlines() if k in line or v['row']['title'].lower() in line.lower()]
   found.append({'id':k,'path':str(p),'sha256':hashlib.sha256(s.encode()).hexdigest(),'matches':matches})
(L/'outputs/history.json').write_text(json.dumps({'scanned_files':scanned,'scope':str(R),'matches':found},indent=2));print('files',scanned,'matches',[(x['id'],x['path']) for x in found])
