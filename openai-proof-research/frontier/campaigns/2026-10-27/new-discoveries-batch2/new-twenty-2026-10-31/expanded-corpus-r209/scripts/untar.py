import sys,tarfile,gzip,io,os
from pathlib import Path
L=Path(sys.argv[1]).resolve()
for d in sorted((L/'sources').glob('src-*')):
    b=(d/'body').read_bytes()
    out=d/'extracted'
    if out.exists(): continue
    out.mkdir()
    try: raw=gzip.decompress(b)
    except Exception: raw=b
    try:
        t=tarfile.open(fileobj=io.BytesIO(raw))
        for m in t.getmembers():
            if not m.isfile(): continue
            name=m.name.replace('/','__').replace('..','_')
            if not name.endswith(('.tex','.bbl','.sty','.txt')): continue
            (out/name).write_bytes(t.extractfile(m).read())
    except tarfile.ReadError:
        (out/'main.tex').write_bytes(raw)
    print(d.name, os.listdir(out))
