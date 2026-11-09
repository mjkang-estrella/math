from pathlib import Path
import json,hashlib,tarfile,gzip,io
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Packet contains source and original development logs, never compiled artifacts.
exclude={'source-only.tar.gz','archive-receipt.json','final-manifest.json','final-verification-receipt.json'}
files=[p for p in sorted(L.rglob('*')) if p.is_file() and p.name not in exclude
       and 'fresh-replay' not in p.relative_to(L).parts and p.suffix not in {'.olean','.ilean','.c','.o'}]
with (L/'source-only.tar.gz').open('wb') as raw:
    with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as gz:
        with tarfile.open(fileobj=gz,mode='w',format=tarfile.PAX_FORMAT) as tar:
            for p in files:
                t=tarfile.TarInfo(str(p.relative_to(L))); data=p.read_bytes()
                t.size=len(data);t.mode=0o644;t.uid=t.gid=t.mtime=0;t.uname=t.gname=''
                tar.addfile(t,io.BytesIO(data))
(L/'archive-receipt.json').write_text(json.dumps({'archive_sha256':sha(L/'source-only.tar.gz'),
 'members':{str(p.relative_to(L)):sha(p) for p in files},'source_only':True},indent=2)+'\n')
d=L/'fresh-replay'; d.mkdir()
with tarfile.open(L/'source-only.tar.gz') as tar:tar.extractall(d,filter='data')
print('source-only archive and fresh extraction prepared')
