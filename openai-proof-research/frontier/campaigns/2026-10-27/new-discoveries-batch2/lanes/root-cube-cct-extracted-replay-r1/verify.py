import sys,hashlib,json,tarfile,io
from pathlib import Path
root=Path(__file__).parent
src=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-cube-cct-source-formal-r1/source-only.tar.gz")
expected="ead8a07b9a339d55285f12e37f96fb6834a58007988160e8df8a8a864e3c595d"
digest=lambda b:hashlib.sha256(b).hexdigest()
if sys.argv[1]=="prepare":
 data=src.read_bytes();assert digest(data)==expected
 (root/"frozen.tar.gz").write_bytes(data)
 out=root/"extracted";out.mkdir()
 files={}
 with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as tf:
  for m in tf.getmembers():
   p=Path(m.name)
   assert not p.is_absolute() and ".." not in p.parts and m.isfile(),m.name
   assert p.suffix not in {".olean",".ilean",".o"},m.name
   raw=tf.extractfile(m).read();dest=out/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw);files[m.name]=digest(raw)
 (root/"freeze.json").write_text(json.dumps({"archive":expected,"files":files},indent=2)+"\n")
 print("PASS safe source-only extraction",len(files))
else:
 f=json.loads((root/"freeze.json").read_text());out=root/"extracted"
 assert digest(src.read_bytes())==f["archive"]==digest((root/"frozen.tar.gz").read_bytes())
 for n,h in f["files"].items():assert digest((out/n).read_bytes())==h,n
 guards={p.name:json.loads(p.read_text()) for p in out.glob("*.guard.json")}
 assert len(guards)==4
 assert all(g["exit_code"]==0 and g["reason"] is None for g in guards.values())
 receipt=json.loads((out/"replay-receipt.json").read_text())
 result={"status":"PASS","original_archive_unchanged":True,"source_files_unchanged":len(f["files"]),"guards":guards,"audit_receipt":receipt}
 (root/"ROOT-REPLAY-RECEIPT.json").write_text(json.dumps(result,indent=2)+"\n")
 print(json.dumps({"status":"PASS","source_files":len(f["files"]),"receipt":receipt}))
