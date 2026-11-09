from pathlib import Path,PurePosixPath
import sys,zipfile,stat,json,hashlib
src=Path(sys.argv[1]).resolve();dst=Path(sys.argv[2]).resolve()
if dst.exists():raise SystemExit('Destination must not exist')
with zipfile.ZipFile(src) as z:
 names=set()
 for m in z.infolist():
  p=PurePosixPath(m.filename)
  if p.is_absolute() or '..' in p.parts or '\\' in m.filename or m.filename in names or stat.S_ISLNK(m.external_attr>>16) or p.suffix in ['.olean','.ilean','.pyc']:raise SystemExit('Unsafe member: '+m.filename)
  names.add(m.filename)
 if sum(m.file_size for m in z.infolist())>300*1024**2:raise SystemExit('Archive too large')
 dst.mkdir();z.extractall(dst)
receipt={'archive':src.name,'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'members':len(names),'safe':True,'destination':str(dst)}
(dst/'extraction-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
