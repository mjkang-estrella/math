import urllib.request,pathlib,json,hashlib,datetime,re
L=pathlib.Path(__file__).resolve().parents[1];rs=[]
urls=[
('chessboard.html','https://link.springer.com/article/10.1007/s00236-026-00547-w'),
('openai-tree.json','https://api.github.com/repos/openai/math/git/trees/4eaee87548250b2682affda7d05d947c05554bae?recursive=1'),
('grid.pdf','https://arxiv.org/pdf/2507.16469'),
('shortcycles.pdf','https://citeseerx.ist.psu.edu/document?doi=87605ce797952c917691cde70f90c3ce0ef5381c&repid=rep1&type=pdf')]
for name,url in urls:
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research evidence'}),timeout=20) as s:d=s.read();status=s.status
  (L/'sources'/name).write_bytes(d);rs.append(dict(file=name,url=url,status=status,sha256=hashlib.sha256(d).hexdigest(),bytes=len(d),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:rs.append(dict(file=name,url=url,error=str(e)))
 (L/'outputs/final-receipts.json').write_text(json.dumps(rs,indent=2))
 print(rs[-1],flush=True)
