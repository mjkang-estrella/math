from pathlib import Path
import json,hashlib,zipfile,sys
r=Path(__file__).resolve().parent
if sys.argv[1]=='preserve':
 b=(r/'results.json').read_bytes();(r/'scaling-measurements.json').write_bytes(b);assert hashlib.sha256(b).digest()==hashlib.sha256((r/'scaling-measurements.json').read_bytes()).digest()
else:
 dst=r/'strict-final';assert not dst.exists();dst.mkdir()
 with zipfile.ZipFile(r/'source-only.zip') as z:
  for n in z.namelist():
   p=Path(n);assert not p.is_absolute() and '..' not in p.parts
  z.extractall(dst)
 for line in (dst/'source-manifest.sha256').read_text().splitlines():
  h,n=line.split('  ',1);assert hashlib.sha256((dst/n).read_bytes()).hexdigest()==h
 print('Safe extraction and full source manifest checked')
