import sys,tarfile,gzip,io,pathlib
# usage: untar_all.py SRCDIR OUTROOT id1 id2 ... ; each extracted into fresh OUTROOT/id (must not exist)
src=pathlib.Path(sys.argv[1]); root=pathlib.Path(sys.argv[2])
for i in sys.argv[3:]:
  b=src/f'src-{i}.bin'; out=root/i; out.mkdir(parents=True,exist_ok=False)
  data=b.read_bytes()
  try: data=gzip.decompress(data)
  except Exception: pass
  try:
    tf=tarfile.open(fileobj=io.BytesIO(data)); n=0
    for m in tf.getmembers():
      if not m.isfile(): continue
      name=pathlib.PurePosixPath(m.name)
      if name.is_absolute() or '..' in name.parts: continue
      if name.suffix.lower() not in ('.tex','.bbl','.sty','.txt','.bib',''): continue
      (out/('__'.join(name.parts))).write_bytes(tf.extractfile(m).read()); n+=1
    print(i,'tar files',n,[p.name for p in out.iterdir()])
  except tarfile.ReadError:
    (out/'main.tex').write_bytes(data); print(i,'single file',len(data))
