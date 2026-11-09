import tarfile,gzip,io,pathlib,sys
L=pathlib.Path(__file__).resolve().parents[1]
for k in sys.argv[1:]:
  src=L/'sources/eprint'/f'{k}.eprint'; dst=L/'sources/eprint'/f'{k}-x'
  dst.mkdir(exist_ok=False)
  raw=gzip.decompress(src.read_bytes())
  try:
    with tarfile.open(fileobj=io.BytesIO(raw)) as t:
      t.extractall(dst,filter='data')
  except tarfile.ReadError:
    (dst/'main.tex').write_bytes(raw)
  print(k,[str(p.relative_to(dst)) for p in dst.rglob('*') if p.is_file()][:30])
