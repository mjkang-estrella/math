from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,subprocess
L=Path(__file__).resolve().parents[1];(L/'sources').mkdir(exist_ok=True)
urls={'dismal.pdf':'https://neilsloane.com/doc/carry2.pdf','saturated.pdf':'https://arxiv.org/pdf/0909.1970','quandle-original.pdf':'https://arxiv.org/pdf/1407.5803','quandle-successor.html':'https://pmc.ncbi.nlm.nih.gov/articles/PMC8023397/','walk-report.html':'https://ems.press/journals/owr/articles/14299904'}
rows=[]
for name,url in urls.items():
 row={'url':url,'file':'sources/'+name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as r: b=r.read(); row.update(status=r.status,final_url=r.url)
  (L/row['file']).write_bytes(b);row.update(size=len(b),sha256=hashlib.sha256(b).hexdigest());print(name,len(b))
 except Exception as e:
  row['error']=repr(e);print(name,repr(e))
 rows.append(row);(L/'source-provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
 if row.get('status') in [403,429] or '403' in row.get('error','') or '429' in row.get('error',''):break
for row in rows:
 if row.get('status')==200 and row['file'].endswith('.pdf'):
  subprocess.run(['pdftotext','-layout',str(L/row['file']),str(L/'work'/(Path(row['file']).stem+'.txt'))],check=True)
