import pathlib,gzip,shutil
L=pathlib.Path(__file__).resolve().parent
with (L/'Audit.log').open('rb') as a,(L/'attempt07-wide-audit.log.gz').open('wb') as b:
 with gzip.GzipFile(filename='',fileobj=b,mode='wb',mtime=0) as g:shutil.copyfileobj(a,g,1024*1024)
for s in ['guard.json','console']:(L/('Audit.'+s)).rename(L/('attempt07-wide-audit.'+s))
(L/'Audit.log').unlink()
