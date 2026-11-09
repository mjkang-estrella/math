"""Extract a bounded source archive into a NEW directory, refusing unsafe names."""
from pathlib import Path,PurePosixPath
import sys,zipfile,stat,json,hashlib
archive=Path(sys.argv[1]);dest=Path(sys.argv[2]);assert not dest.exists(),'destination exists'
with zipfile.ZipFile(archive) as z:
 infos=z.infolist();assert len(infos)<100 and len({i.filename for i in infos})==len(infos)
 assert sum(i.file_size for i in infos)<8*1024**2
 for i in infos:
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
  assert not stat.S_ISLNK(i.external_attr>>16) and not i.is_dir()
  assert not any(x.endswith(('.olean','.ilean','.so','.pyc')) for x in p.parts)
 dest.mkdir(parents=True)
 for i in infos:
  out=dest/i.filename;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(z.read(i))
print(json.dumps({'status':'PASS','archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'files':len(infos),'destination':str(dest)}))
