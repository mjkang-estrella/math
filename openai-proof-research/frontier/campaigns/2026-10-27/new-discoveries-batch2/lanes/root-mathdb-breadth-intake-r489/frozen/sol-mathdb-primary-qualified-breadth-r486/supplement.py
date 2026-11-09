from pathlib import Path
import json,urllib.request,datetime,hashlib,subprocess
O=Path(__file__).resolve().parent;L=O.parent
x=json.loads((L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text())
def walk(v):
 if isinstance(v,dict):
  if '344947' in json.dumps(v) and ('mathdb_id' in v or 'mathdb_ids' in v):print('HISTORICAL',json.dumps(v,ensure_ascii=False))
  else:
   for w in v.values():walk(w)
 elif isinstance(v,list):
  for w in v:walk(w)
walk(x)
a=[]
for stem,ids in [('2005.02141v1',[346369]),('1907.00847',[344866])]:
 e=dict(url='https://arxiv.org/pdf/'+stem,ids=ids,access_date=datetime.datetime.now(datetime.timezone.utc).isoformat());a.append(e)
 try:
  with urllib.request.urlopen(e['url'],timeout=12) as r:d=r.read();e.update(http_status=r.status,final_url=r.url)
  p=O/'sources'/f'{stem}.pdf';p.write_bytes(d);e.update(path=str(p.resolve()),sha256=hashlib.sha256(d).hexdigest(),size=len(d));(O/'supplement-provenance.json').write_text(json.dumps(a,indent=2)+'\n')
  t=p.with_suffix('.txt');q=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True);e['pdftotext_returncode']=q.returncode
  if q.returncode==0:
   b=t.read_bytes();e.update(text_path=str(t.resolve()),text_sha256=hashlib.sha256(b).hexdigest(),text_size=len(b))
 except Exception as ex:
  e['failure']=str(ex)
  if getattr(ex,'code',None) in (403,429):break
 (O/'supplement-provenance.json').write_text(json.dumps(a,indent=2)+'\n')
print(json.dumps(a,indent=2))
