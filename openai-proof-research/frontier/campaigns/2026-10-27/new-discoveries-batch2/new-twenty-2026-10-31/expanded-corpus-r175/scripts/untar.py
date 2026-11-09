import sys,tarfile,gzip,pathlib,io
src=pathlib.Path(sys.argv[1]); dst=pathlib.Path(sys.argv[2]); dst.mkdir(parents=True,exist_ok=False)
b=src.read_bytes()
try:
    with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as t:
        t.extractall(dst,filter='data')
except tarfile.ReadError:
    d=gzip.decompress(b) if b[:2]==b'\x1f\x8b' else b
    (dst/'main.tex').write_bytes(d)
for p in sorted(dst.rglob('*.tex')): print(p.relative_to(dst.parent), p.stat().st_size)
