#!/usr/bin/env python3
import sys,zipfile,pathlib,stat
archive,dest=map(pathlib.Path,sys.argv[1:]);assert not dest.exists();dest.mkdir()
with zipfile.ZipFile(archive) as z:
 names=set()
 for i in z.infolist():
  p=pathlib.PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
  assert i.filename not in names and not stat.S_ISLNK(i.external_attr>>16)
  assert i.file_size<100*1024**2
  names.add(i.filename)
 z.extractall(dest)
print('Safe extraction:',len(names),'members')
