"""Reproduce safe extraction into an explicitly supplied new lane-local directory."""
from pathlib import Path
import hashlib,zipfile,sys
D=Path(__file__).resolve().parent.parent
z=D.parent/'wheel-formal-r2b/wheel-complete-source.zip'
assert hashlib.sha256(z.read_bytes()).hexdigest()=='f92bef69b502dd3d06b644891e284891b52687f73981022c2141312c3019aa3a'
out=(D/sys.argv[1]).resolve();assert out.is_relative_to(D) and not out.exists();out.mkdir()
with zipfile.ZipFile(z) as f:
 for i in f.infolist():
  p=Path(i.filename)
  assert not p.is_absolute() and '..' not in p.parts
  assert (i.external_attr>>16)&0o170000!=0o120000
  assert p.suffix not in ['.olean','.ilean']
 f.extractall(out)
