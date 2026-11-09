import pathlib,urllib.request,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1];rs=[]
urls=[
('kitaev-publications','https://spider-v.science.strath.ac.uk/sergey.kitaev/publications.html'),
('broere-thesis.pdf','https://www.math.ru.nl/~bosma/Students/BasBroereMSc.pdf'),
('hefty.pdf','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v31i4p2/pdf/'),
('product-cube.abs','https://arxiv.org/abs/1808.01800'),
('product-cube.pdf','https://arxiv.org/pdf/1808.01800'),
]
omega=json.loads((L/'sources/omega-head').read_text())['sha']
urls.append(('omega-tree.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{omega}?recursive=1'))
for name,url in urls:
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research evidence'}),timeout=18) as s:d=s.read();status=s.status
  (L/'sources'/name).write_bytes(d);rs.append(dict(name=name,url=url,status=status,sha256=hashlib.sha256(d).hexdigest(),bytes=len(d)))
 except Exception as e:rs.append(dict(name=name,url=url,error=str(e)))
 rs[-1]['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 (L/'outputs/more-receipts.json').write_text(json.dumps(rs,indent=2))
 print(rs[-1],flush=True)
