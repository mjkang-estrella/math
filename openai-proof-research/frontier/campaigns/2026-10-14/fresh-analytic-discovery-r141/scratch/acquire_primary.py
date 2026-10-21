from pathlib import Path
import urllib.request,hashlib,json,tarfile,gzip,io,concurrent.futures,subprocess,datetime
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-analytic-discovery-r141');D=R/'private/primary';D.mkdir(exist_ok=True)
items=[('fish','https://arxiv.org/src/1605.01702v2'),('saga','https://arxiv.org/src/1801.06200v2'),('beltrami','https://arxiv.org/src/2111.03559v3'),('bessa','https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/j.crma.2008.07.012.pdf'),('bgh','https://citeseerx.ist.psu.edu/document?doi=c8be492735190741b1de99fd2c89c374702f22b5&repid=rep1&type=pdf')]
def get(item):
 name,url=item;q=D/name;q.mkdir(exist_ok=True);row={'name':name,'url':url,'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  resp=urllib.request.urlopen(url,timeout=45);b=resp.read();row.update(status=resp.status,final_url=resp.url,raw_sha256=hashlib.sha256(b).hexdigest(),raw_size=len(b));(q/'raw').write_bytes(b)
  members=[]
  if b.startswith(b'%PDF'):
   (q/'paper.pdf').write_bytes(b);subprocess.run(['pdftotext','-layout',str(q/'paper.pdf'),str(q/'paper.txt')],check=True)
   members=['paper.pdf','paper.txt']
  else:
   try:
    t=tarfile.open(fileobj=io.BytesIO(b),mode='r:*')
    for m in t.getmembers():
     if m.isfile() and m.name.endswith(('.tex','.bib','.bbl')):
      path=Path(m.name)
      if path.is_absolute() or '..' in path.parts:raise ValueError('unsafe archive path')
      dest=q/'extracted'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(t.extractfile(m).read());members.append(str(dest.relative_to(q)))
   except tarfile.ReadError:
    payload=gzip.decompress(b) if b.startswith(b'\x1f\x8b') else b
    (q/'extracted.tex').write_bytes(payload);members=['extracted.tex']
  row['members']=[{'path':str((q/n).relative_to(R)),'size':(q/n).stat().st_size,'sha256':hashlib.sha256((q/n).read_bytes()).hexdigest()} for n in members]
 except Exception as e:row['error']=repr(e)
 row['end_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();return row
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:rows=list(ex.map(get,items))
(R/'primary-authentication.json').write_text(json.dumps(rows,indent=2)+'\n')
for x in rows:
 print(x['name'],x.get('status'),x.get('error'),[(m['path'],m['size']) for m in x.get('members',[])])
