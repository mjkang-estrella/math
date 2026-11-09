import os, subprocess, re
from pathlib import Path
lane=Path(__file__).resolve().parent.parent
pkg=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages")
count=200
def build(src,out,root=None):
 global count
 for attempt in range(60):
  count+=1
  cmd=[str(lane/"scripts/lean.sh")]
  if root: cmd+=["--root="+str(root)]
  cmd+=["-o",str(out),str(src)]
  r=subprocess.run(cmd,cwd=lane,capture_output=True,text=True)
  log=lane/"logs"/("build-%03d.log"%count); log.write_text(r.stdout+r.stderr)
  print(log.name,r.returncode,flush=True)
  if r.returncode==0:return
  text=r.stdout+r.stderr
  m=re.search(r"(?:failed to read file|object file) '([^']+?\.olean)(?:\.private)?'",text)
  if not m: print(text); raise SystemExit(1)
  f=Path(m[1])
  package="mathlib"
  module=f.relative_to(lane/"build") if f.is_relative_to(lane/"build") else Path(str(f).split("/.lake/build/lib/lean/")[1])
  target=lane/"build"/module
  target.parent.mkdir(parents=True,exist_ok=True)
  for old in target.parent.glob(target.name+"*"):
   if old.is_symlink(): old.unlink()
  source=pkg/package/module.with_suffix(".lean")
  build(source,target,pkg/package)
 raise SystemExit("repair limit")
build(lane/"src/GridBasic.lean",lane/"build/GridBasic.olean")
