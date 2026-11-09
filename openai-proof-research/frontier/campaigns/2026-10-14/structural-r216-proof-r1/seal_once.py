from pathlib import Path
import hashlib, json, os, stat
ROOT=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
OWN=ROOT/"frontier/campaigns/2026-10-14/structural-r216-proof-r1"
for name in ["MANIFEST.json","SELECTION.json","ANCHORS.json","SEALED-ONCE"]:
    if (OWN/name).exists(): raise RuntimeError("Refuse reseal: "+name)
# Only the reviewer's exact workspace; never author inputs or broad history.
for directory, dirs, files in os.walk(OWN,followlinks=False):
    Path(directory).chmod(0o700)
    for name in dirs+files:
        p=Path(directory)/name
        if p.is_symlink(): raise RuntimeError("symlink in own workspace")
        p.chmod(0o700 if p.is_dir() else 0o600)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
packet=OWN/"packet"; entries=[]
for directory, dirs, files in os.walk(packet,followlinks=False):
    for name in dirs+files:
        p=Path(directory)/name
        e={"path":p.relative_to(packet).as_posix(),"kind":"dir" if p.is_dir() else "file","mode":format(stat.S_IMODE(p.stat().st_mode),"04o")}
        if e["kind"]=="file": e.update(bytes=p.stat().st_size,sha256=sha(p))
        entries.append(e)
entries.sort(key=lambda e:e["path"])
selection=[{k:e[k] for k in ("path","kind","mode")} for e in entries]
def write_new(name,value):
    p=OWN/name
    with p.open("x") as f: f.write(json.dumps(value,indent=2,ensure_ascii=False)+"\n")
    p.chmod(0o600)
write_new("SELECTION.json",selection)
write_new("MANIFEST.json",{"schema":1,"packet_root_mode":"0700","selection_sha256":sha(OWN/"SELECTION.json"),"entries":entries})
anchors={"FINAL":sha(packet/"FINAL.md"),"MANIFEST":sha(OWN/"MANIFEST.json"),"SELECTION":sha(OWN/"SELECTION.json"),"REPORT":sha(OWN/"REPORT.md"),"VERIFIER":sha(OWN/"verify_packet.py")}
write_new("ANCHORS.json",anchors)
with (OWN/"SEALED-ONCE").open("x") as f:f.write("Exact review packet sealed once. Never edit selected bytes/modes or reseal.\n")
(OWN/"SEALED-ONCE").chmod(0o600)
print(json.dumps({"files":sum(e["kind"]=="file" for e in entries),"entries":len(entries),"anchors":anchors},indent=2))
