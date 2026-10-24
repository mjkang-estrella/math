from pathlib import Path
import argparse,hashlib,json,os,stat
p=argparse.ArgumentParser(description="Read-only artifact verification; not a mathematical gate")
p.add_argument("--packet",required=True);p.add_argument("--manifest",required=True)
p.add_argument("--manifest-sha256",required=True);p.add_argument("--final-sha256",required=True)
p.add_argument("--report",required=True);p.add_argument("--report-sha256",required=True)
a=p.parse_args()
def digest(b):return hashlib.sha256(b).hexdigest()
root=Path(a.packet);manifest=Path(a.manifest);report=Path(a.report)
assert digest(manifest.read_bytes())==a.manifest_sha256,"MANIFEST anchor mismatch"
assert digest((root/"FINAL.md").read_bytes())==a.final_sha256,"FINAL anchor mismatch"
assert digest(report.read_bytes())==a.report_sha256,"REPORT anchor mismatch"
m=json.loads(manifest.read_bytes());assert m["format"]=="r219-exact-selection-v1"
actual={}
assert not root.is_symlink() and stat.S_IMODE(root.stat().st_mode)==0o700,"packet root mode"
for parent,dirs,files in os.walk(root,followlinks=False):
 for name in dirs+files:
  q=Path(parent)/name;assert not q.is_symlink(),"symlink in packet"
  rel=q.relative_to(root).as_posix();st=q.stat()
  if q.is_dir():actual[rel]={"type":"directory","mode":format(stat.S_IMODE(st.st_mode),"04o")}
  else:
   assert q.is_file(),"nonregular packet entry"
   b=q.read_bytes();actual[rel]={"type":"file","mode":format(stat.S_IMODE(st.st_mode),"04o"),"bytes":len(b),"sha256":digest(b)}
assert actual==m["entries"],"exact selection, content or mode mismatch"
assert stat.S_IMODE(manifest.stat().st_mode)==0o600,"manifest mode"
assert stat.S_IMODE(report.stat().st_mode)==0o600,"report mode"
print(json.dumps({"artifact_verification":"passed","files":sum(v["type"]=="file" for v in actual.values()),"directories":sum(v["type"]=="directory" for v in actual.values()),"read_only":True,"mathematical_gate":False}))
