import pathlib,gzip,tarfile,io,json
D=pathlib.Path(__file__).resolve().parents[1]; S=D/'sources'; U=S/'unpacked'; U.mkdir(exist_ok=True)
for p in sorted(S.glob('*.eprint')):
 k=p.name[:-7]; o=U/k; o.mkdir(exist_ok=True); b=p.read_bytes()
 try: raw=gzip.decompress(b)
 except Exception: raw=b
 try:
  with tarfile.open(fileobj=io.BytesIO(raw)) as t:
   for m in t.getmembers():
    if m.isfile() and not m.name.startswith('/') and '..' not in m.name:
     q=o/m.name.replace('/','__'); q.write_bytes(t.extractfile(m).read())
  print(k,'tar',[x.name for x in o.iterdir()])
 except tarfile.ReadError:
  (o/'main.tex').write_bytes(raw); print(k,'single',len(raw))
