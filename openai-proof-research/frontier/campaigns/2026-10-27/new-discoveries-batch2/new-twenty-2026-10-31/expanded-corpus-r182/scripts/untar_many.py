import sys,tarfile,gzip,io,pathlib
L=pathlib.Path(sys.argv[1])
for i in sys.argv[2:]:
    src=L/f'sources/eprint-{i}.tgz'; dst=L/f'sources/tex-{i}'; dst.mkdir(parents=True,exist_ok=False)
    b=src.read_bytes()
    try:
        t=tarfile.open(fileobj=io.BytesIO(b),mode='r:*')
        for m in t.getmembers():
            if m.isfile() and m.name.endswith(('.tex','.bbl','.sty','.txt')):
                t.extract(m,dst,filter='data')
        print(i,'tar',[m.name for m in t.getmembers() if m.isfile() and m.name.endswith('.tex')])
    except tarfile.ReadError:
        d=gzip.decompress(b) if b[:2]==b'\x1f\x8b' else b
        (dst/'main.tex').write_bytes(d); print(i,'single file',len(d))
