from pathlib import Path
import hashlib,json,collections
p=Path(__file__).resolve().parent.parent
def sha(q):
 h=hashlib.sha256()
 with q.open("rb") as f:
  for chunk in iter(lambda:f.read(1024*1024),b""): h.update(chunk)
 return h.hexdigest()
active=sorted((p/"logs").glob("*_terminal-seal.log"))
assert len(active)==1
log=active[0]; receipt=p/"receipt"/(log.stem+".json")
assert not receipt.exists()
exclusions=["SHA256-MANIFEST.json",str(log.relative_to(p)),str(receipt.relative_to(p))]
after=json.loads((p/"frozen-after.json").read_text())
assert after["count"]==552 and after["mismatches"]==[]
completed=[]
for q in sorted((p/"receipt").glob("*.json")):
 r=json.loads(q.read_text()); assert r["group_members_left"]==[]
 assert sha(Path(r["log"]))==r["log_sha256"]
 completed.append({"path":str(q.relative_to(p)),"sha256":sha(q),"exit":r["exit"],"label":r["label"]})
files={}
for q in sorted(p.rglob("*")):
 if not q.is_file(): continue
 rel=str(q.relative_to(p))
 if rel not in exclusions: files[rel]=sha(q)
manifest={"files":files,"completed_runner_receipts":completed,"bootstrap_receipt":{"path":"bootstrap-receipt.json","sha256":sha(p/"bootstrap-receipt.json")},"frozen_after":after,"terminal_self_exclusions":exclusions,"self_exclusion_reason":"Manifest cannot hash itself; current runner log is open and current receipt does not exist until this child exits. ALL already completed receipt JSONs, including copied historical receipts, are included in files.","all_completed_groups_empty":True,"exit_counts":dict(collections.Counter(str(r["exit"]) for r in completed))}
(p/"SHA256-MANIFEST.json").write_text(json.dumps(manifest,indent=2))
# Verify completed files after writing; terminal log/receipt deliberately excluded.
assert all(sha(p/n)==h for n,h in files.items())
print(json.dumps({"manifest_files":len(files),"completed_runner_receipts":len(completed),"bootstrap_included":True,"frozen_after":after,"self_exclusions":exclusions,"all_hashes_reverified":True,"manifest_sha256":sha(p/"SHA256-MANIFEST.json")}))
