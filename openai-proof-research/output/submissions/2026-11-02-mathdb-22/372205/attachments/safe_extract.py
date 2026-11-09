#!/usr/bin/env python3
import sys,zipfile,stat
from pathlib import Path
archive,destination=map(Path,sys.argv[1:])
if destination.exists(): raise SystemExit('Destination must not exist')
with zipfile.ZipFile(archive) as z:
 names=set()
 for i in z.infolist():
  p=Path(i.filename)
  if p.is_absolute() or '..' in p.parts or '\\' in i.filename or i.filename in names or stat.S_ISLNK(i.external_attr>>16) or '.olean' in p.suffixes: raise SystemExit('Unsafe archive member: '+i.filename)
  names.add(i.filename)
 destination.mkdir()
 z.extractall(destination)
print('SAFE_EXTRACTION_PASS',len(names))
