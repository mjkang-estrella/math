import sys,tarfile,gzip,io,pathlib
src=pathlib.Path(sys.argv[1]); dst=pathlib.Path(sys.argv[2]); dst.mkdir(parents=True,exist_ok=False)
b=src.read_bytes()
try:
    t=tarfile.open(fileobj=io.BytesIO(b),mode='r:*')
    for m in t.getmembers():
        if m.isfile() and (m.name.endswith(('.tex','.bbl','.sty','.txt'))):
            t.extract(m,dst,filter='data')
    print(src.name,'tar',[m.name for m in t.getmembers() if m.isfile()][:30])
except tarfile.ReadError:
    d=gzip.decompress(b) if b[:2]==b'\x1f\x8b' else b
    (dst/'main.tex').write_bytes(d); print(src.name,'single file',len(d))
