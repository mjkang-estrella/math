import sys,json,hashlib,os,stat
from pathlib import Path
root=Path(sys.argv[1]); anchors=sys.argv[2:]
assert len(anchors)==3,"require detached FINAL MANIFEST REPORT SHA256 anchors"
envelopes=["FINAL.md","MANIFEST.json","REPORT.md"]
for name,anchor in zip(envelopes,anchors):
 p=root/name;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
 assert hashlib.sha256(p.read_bytes()).hexdigest()==anchor,name
m=json.loads((root/"MANIFEST.json").read_text());files={};dirs=[]
for base,ds,fs in os.walk(root,followlinks=False):
 for name in ds:
  p=Path(base)/name;assert not p.is_symlink();dirs.append(p.relative_to(root).as_posix())
 for name in fs:
  p=Path(base)/name;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
  rel=p.relative_to(root).as_posix()
  if rel in envelopes:continue
  b=p.read_bytes();files[rel]={"bytes":len(b),"sha256":hashlib.sha256(b).hexdigest()}
assert files==m["files"],"exact payload mismatch"
assert sorted(dirs)==m["directories"],"exact directories mismatch"
print("artifact bytes and membership match detached anchors; no mathematical gate")
