import pathlib,sys,zipfile,stat
archive=pathlib.Path(sys.argv[1]);dest=pathlib.Path(sys.argv[2]).resolve()
assert not dest.exists(), "destination must be new"
with zipfile.ZipFile(archive) as z:
 for i in z.infolist():
  p=pathlib.PurePosixPath(i.filename)
  assert not p.is_absolute() and ".." not in p.parts and "\\" not in i.filename
  assert not stat.S_ISLNK(i.external_attr >> 16)
  assert p.suffix not in {".olean", ".ilean", ".so"}, "compiled payload refused"
 dest.mkdir(parents=True)
 z.extractall(dest)
print(dest)
