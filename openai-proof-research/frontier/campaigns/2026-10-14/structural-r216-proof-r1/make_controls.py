from pathlib import Path
import hashlib, json, os, subprocess, sys
ROOT=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
OWN=ROOT/"frontier/campaigns/2026-10-14/structural-r216-proof-r1"
C=OWN/"tiny-controls"; C.mkdir(mode=0o700)
p=C/"packet"; p.mkdir(mode=0o700)
(p/"FINAL.md").write_text("Tiny independent verifier control.\n")
(p/"payload.txt").write_text("Original tiny payload.\n")
for f in p.iterdir(): f.chmod(0o600)
(C/"REPORT.md").write_text("Artifact fixture only; no mathematical verdict.\n")
def h(f): return hashlib.sha256(f.read_bytes()).hexdigest()
entries=[{"path":f.name,"kind":"file","mode":"0600","bytes":f.stat().st_size,"sha256":h(f)} for f in sorted(p.iterdir())]
s=[{k:e[k] for k in ("path","kind","mode")} for e in entries]
(C/"SELECTION.json").write_text(json.dumps(s,indent=2)+"\n")
(C/"MANIFEST.json").write_text(json.dumps({"selection_sha256":h(C/"SELECTION.json"),"entries":entries},indent=2)+"\n")
args=[sys.executable,"-B",str(OWN/"verify_packet.py"),"--packet",str(p),"--manifest",str(C/"MANIFEST.json"),"--selection",str(C/"SELECTION.json"),"--report",str(C/"REPORT.md"),"--final-sha",h(p/"FINAL.md"),"--manifest-sha",h(C/"MANIFEST.json"),"--selection-sha",h(C/"SELECTION.json"),"--report-sha",h(C/"REPORT.md")]
results=[]
def run(label,expected):
    q=subprocess.run(args,cwd=ROOT,text=True,capture_output=True,timeout=10)
    assert q.returncode==expected,(label,q.stdout,q.stderr)
    results.append({"case":label,"exit_code":q.returncode,"output":q.stdout.strip()})
run("pristine independent two-file fixture",0)
f=p/"payload.txt"; original=f.read_bytes(); f.write_bytes(original+b"changed\n")
run("changed selected payload bytes",1); f.write_bytes(original)
f.chmod(0o644); run("changed selected payload mode",1); f.chmod(0o600)
(p/"extra.txt").write_text("extra\n"); run("unexpected packet file",1); (p/"extra.txt").unlink()
(OWN/"CONTROL-RESULTS.json").write_text(json.dumps({"controls":results,"mathematical_gate":False,"fixture_files":2,"fixture_payload_bytes":sum(f.stat().st_size for f in p.iterdir()),"author_manifest_reused":False},indent=2)+"\n")
print(json.dumps(results))
