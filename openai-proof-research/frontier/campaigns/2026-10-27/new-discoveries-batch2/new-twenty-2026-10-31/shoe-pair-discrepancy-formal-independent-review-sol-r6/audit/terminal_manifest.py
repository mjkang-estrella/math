from pathlib import Path
import json,hashlib,subprocess
lane=Path.cwd()
active=list(Path("logs").glob("*_terminal_manifest.log"))
assert len(active)==1
log=active[0]; receipt="receipt/"+log.stem+".json"
excluded={"SHA256-MANIFEST.json","TERMINAL-EXCLUSIONS.json",str(log),receipt}
files={}
for base in [lane]:
 for p in base.rglob("*"):
  if p.is_symlink(): raise RuntimeError("No symlink traversal in terminal manifest")
  if not p.is_file(): continue
  rel=str(p.relative_to(lane))
  if rel in excluded: continue
  h=hashlib.sha256()
  with p.open("rb") as f:
   for b in iter(lambda:f.read(65536),b""): h.update(b)
  files[rel]=h.hexdigest()
obj={"files":files,"terminal_non_circular_exclusions":"TERMINAL-EXCLUSIONS.json is the exact terminal declaration; it also names the final receipt-driven display audit file created after this snapshot.","known_terminal_exclusions":sorted(excluded),"scope":"Entire exclusive own lane, including frozen copies/helpers/pins/plans/source/build/replay/logs/completed receipts/audit/renders/reports; no external traversal."}
subprocess.run(["python3","-I","-B","write_lane.py","SHA256-MANIFEST.json"],input=json.dumps(obj,sort_keys=True,indent=2),text=True,check=True)
print("MANIFEST_FILES",len(files))
print("KNOWN_TERMINAL_EXCLUSIONS",sorted(excluded))
print("MANIFEST_SHA256",hashlib.sha256(Path("SHA256-MANIFEST.json").read_bytes()).hexdigest())

