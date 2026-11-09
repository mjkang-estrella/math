from pathlib import Path
import urllib.request,urllib.parse,urllib.error,json,hashlib,datetime
L=Path(__file__).resolve().parent
queries=['"Factors of some truncated basic hypergeometric series"','"Guo" "Conjecture 6.1"']
rows=[]
for i,q in enumerate(queries):
 url='https://arxiv.org/search/?'+urllib.parse.urlencode(dict(query=q,searchtype='all',abstracts='show',order='-announced_date_first',size=50))
 row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalSourceReview/1.0'}),timeout=25) as r:data=r.read(1500000);row['status']=r.status
  p=L/'retrieval'/f'search{i}.html';p.parent.mkdir(exist_ok=True);p.write_bytes(data)
  h=hashlib.sha256(data).hexdigest();dest=L/'search-frozen'/p.name;dest.parent.mkdir(exist_ok=True);dest.write_bytes(data)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==hashlib.sha256(dest.read_bytes()).hexdigest()==h
  row.update(original=str(p),copy=str(dest.relative_to(L)),sha256=h,bytes=len(data))
 except Exception as e:row.update(error=str(e))
 rows.append(row)
 if row.get('status') in [403,429] or '403' in row.get('error','') or '429' in row.get('error',''):break
(L/'search-provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
