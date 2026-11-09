from pathlib import Path
import json,urllib.request,datetime,hashlib,subprocess
O=Path(__file__).resolve().parent; S=O/'sources';S.mkdir(exist_ok=True)
rows=json.loads((O/'assigned-records.json').read_text()); urls={r['record']['source_url'].replace('/abs/','/pdf/'):[] for r in rows}
for r in rows:urls[r['record']['source_url'].replace('/abs/','/pdf/')].append(r['record']['mathdb_id'])
entries=[];stopped=False
for url,ids in urls.items():
 e=dict(url=url,ids=ids,access_date=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='not_read');entries.append(e)
 if stopped:e['failure']='host parked after access-control/rate response';continue
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=12) as resp:d=resp.read();e['final_url']=resp.url;e['http_status']=resp.status
  p=S/(url.rsplit('/',1)[1]+'.pdf');p.write_bytes(d);e.update(path=str(p.resolve()),size=len(d),sha256=hashlib.sha256(d).hexdigest())
  (O/'source-provenance.json').write_text(json.dumps(entries,indent=2)+'\n') # bind before extraction/read
  out=p.with_suffix('.txt'); z=subprocess.run(['pdftotext','-layout',str(p),str(out)],capture_output=True);e['pdftotext_returncode']=z.returncode
  if z.returncode==0:
   b=out.read_bytes();e.update(text_path=str(out.resolve()),text_size=len(b),text_sha256=hashlib.sha256(b).hexdigest())
  else:e['failure']=z.stderr.decode(errors='replace')
 except Exception as ex:
  e['failure']=str(ex)
  if getattr(ex,'code',None) in (403,429):stopped=True
 (O/'source-provenance.json').write_text(json.dumps(entries,indent=2)+'\n')
 print(ids,e.get('size'),e.get('failure'),flush=True)
