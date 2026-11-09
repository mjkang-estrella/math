from pathlib import Path,PurePosixPath
import zipfile,sys,stat
a,d=Path(sys.argv[1]),Path(sys.argv[2]);assert not d.exists()
with zipfile.ZipFile(a) as z:
 ns=set();total=0
 for i in z.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
  assert i.filename not in ns;ns.add(i.filename)
  assert not stat.S_ISLNK(i.external_attr>>16)
  assert i.file_size<64*1024*1024
  total+=i.file_size
 assert total<256*1024*1024
 d.mkdir();z.extractall(d)
print('PASS: fresh extraction; paths, duplicate names, symlinks and size limits checked')
