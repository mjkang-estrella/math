import sys,tarfile,gzip,io,pathlib
# usage: untar.py BIN OUTDIR  (OUTDIR must not exist); extracts only regular text-like files safely
b=pathlib.Path(sys.argv[1]); out=pathlib.Path(sys.argv[2]); out.mkdir(parents=False,exist_ok=False)
data=b.read_bytes()
try: data=gzip.decompress(data)
except Exception: pass
try:
  tf=tarfile.open(fileobj=io.BytesIO(data))
  for m in tf.getmembers():
    if not m.isfile(): continue
    name=pathlib.PurePosixPath(m.name)
    if name.is_absolute() or '..' in name.parts: continue
    if name.suffix.lower() not in ('.tex','.bbl','.sty','.txt','.bib',''): continue
    t=out/('__'.join(name.parts)); t.write_bytes(tf.extractfile(m).read()); print(t.name,m.size)
except tarfile.ReadError:
  (out/'main.tex').write_bytes(data); print('single file main.tex',len(data))
