"""Fresh ZIP extraction: reject absolute/traversal/symlink/duplicate members."""
import pathlib,sys,zipfile,stat
z=pathlib.Path(sys.argv[1]);dest=pathlib.Path(sys.argv[2]);assert not dest.exists()
with zipfile.ZipFile(z) as f:
 names=set()
 for i in f.infolist():
  p=pathlib.PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
  assert i.filename not in names;names.add(i.filename)
  assert not stat.S_ISLNK(i.external_attr>>16)
 dest.mkdir();f.extractall(dest)
print('SAFE EXTRACTION PASS',len(names))
