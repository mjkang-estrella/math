exec((__import__('pathlib').Path(__file__).with_name('fetch.py')).read_text().split('urls=')[0])
urls={'dismal-successor.pdf':'https://arxiv.org/pdf/1908.05220','crossing-resolved.pdf':'https://arxiv.org/pdf/0907.1599','walk-report.pdf':'https://ems.press/content/serial-article-files/53596'}
rows=json.loads((L/'source-provenance.json').read_text())
for name,url in urls.items():
 row={'url':url,'file':'sources/'+name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as r:b=r.read();row.update(status=r.status,final_url=r.url)
  (L/row['file']).write_bytes(b);row.update(size=len(b),sha256=hashlib.sha256(b).hexdigest());print(name,len(b))
 except Exception as e:row['error']=repr(e);print(name,repr(e))
 rows.append(row);(L/'source-provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
 if '403' in row.get('error','') or '429' in row.get('error',''):break
for row in rows:
 if row.get('status')==200 and row['file'].endswith('.pdf'):
  subprocess.run(['pdftotext','-layout',str(L/row['file']),str(L/'work'/(Path(row['file']).stem+'.txt'))],check=True)
from html.parser import HTMLParser
class Text(HTMLParser):
 def handle_data(self,d): self.out.append(d)
t=Text();t.out=[];t.feed((L/'sources/quandle-successor.html').read_text());(L/'work/quandle-successor.txt').write_text('\n'.join(t.out))
