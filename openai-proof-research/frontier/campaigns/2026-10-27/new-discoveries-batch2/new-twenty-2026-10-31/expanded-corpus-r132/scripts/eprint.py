import pathlib,json,urllib.request,hashlib,datetime,sys,tarfile,gzip,io
D=pathlib.Path(__file__).resolve().parents[1]
def get(a):
 d=D/'downloads'/a.replace('/','_'); d.mkdir(parents=True,exist_ok=True)
 url='https://arxiv.org/e-print/'+a; rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if (d/'receipt.json').exists(): print(a,'cached');return
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source check'}),timeout=30) as r: data=r.read();rec.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'))
  rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  (d/'eprint.bin').write_bytes(data)
  out=d/'x'; out.mkdir(exist_ok=True)
  try:
   with tarfile.open(fileobj=io.BytesIO(data)) as t:
    for m in t.getmembers():
     if m.isfile() and '..' not in m.name and not m.name.startswith('/') and m.name.endswith(('.tex','.bbl','.txt','.sty','.bib')):
      p=out/m.name.replace('/','__'); p.write_bytes(t.extractfile(m).read())
   rec['kind']='tar'
  except tarfile.ReadError:
   try: (out/'main.tex').write_bytes(gzip.decompress(data)); rec['kind']='gz'
   except Exception: rec['kind']='raw'
 except Exception as e: rec['error']=str(e)
 (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n'); print(a,rec.get('status',rec.get('error')),rec.get('kind'),flush=True)
for a in sys.argv[1:]: get(a)
