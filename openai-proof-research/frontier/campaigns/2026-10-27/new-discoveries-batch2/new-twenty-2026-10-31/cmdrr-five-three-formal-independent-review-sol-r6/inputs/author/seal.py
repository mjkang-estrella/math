from pathlib import Path
import json,hashlib,subprocess
p=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/cmdrr-five-three-formal-sol-r4")
def sha(f):
    h=hashlib.sha256()
    with f.open("rb") as r:
        for b in iter(lambda:r.read(65536),b""):h.update(b)
    return h.hexdigest()
def write(n,s):subprocess.run(["python3","-I","-B",str(p/"write_lane.py"),n],input=s,text=True,check=True)
logs=[f for f in (p/"logs").iterdir() if f.name.endswith("_terminal-seal.log")]
assert len(logs)==1
self_log=logs[0]
self_receipt=p/"receipt"/(self_log.stem+".json")
exclude=["SHA256-MANIFEST.json",str(self_log.relative_to(p)),str(self_receipt.relative_to(p))]
frozen=json.loads((p/"frozen-after.json").read_text())
assert frozen["mismatches"]==[]
assert frozen["count"]==707
result=json.loads((p/"results/326555.json").read_text())
result["frozen_after"]=frozen
result["terminal_self_exclusions"]=exclude
result["receipt_inventory_scope"]="Snapshot through finalize-full-endpoint-state; later completed receipts/logs are fully inventoried and hashed in terminal SHA256-MANIFEST.json. Its own log/receipt are exact terminal self-exclusions."
result["process_inventory"]="audit/PROCESS-INVENTORY.json and audit/displays/"
write("results/326555.json",json.dumps(result,indent=1)+"\n")
paths=set()
origins=json.loads((p/"INPUT-ORIGINS.json").read_text())
for rel in origins:
    q=p/rel
    assert q.resolve().is_relative_to(p)
    if q.is_file():paths.add(q)
for key in json.loads((p/"frozen-inputs.json").read_text()):
    q=Path(key)
    if q.is_relative_to(p):
        assert q.resolve().is_relative_to(p)
        if q.is_file(): paths.add(q)
# Explicit own-directory enumeration only; no recursive inventory or parent/peer access.
dirs=["","src","build","audit","audit/displays","receipt","logs","tmp","cache","results",
"manuscript","output","output/pdf","controls-negative","extracted-r4","extracted-r4/src","extracted-r4/build"]
known_dirs={p/d for d in dirs}
known_dirs.add(p/"inputs")
for d in dirs:
    folder=p/d
    for f in folder.iterdir():
        assert f.resolve().is_relative_to(p)
        if f.is_file():paths.add(f)
        elif f.is_dir():assert f in known_dirs,("unaccounted own directory",str(f))
all_receipts=[]
for f in (p/"receipt").iterdir():
    if f.suffix==".json":
        r=json.loads(f.read_text())
        assert r.get("group_members_left",[])==[],f
        all_receipts.append(dict(path=str(f.relative_to(p)),sha256=sha(f),exit=r.get("exit"),
            label=r.get("label"),group_members_left=r.get("group_members_left",[])))
inventory=dict(completed_receipts=all_receipts,terminal_receipt_excluded=str(self_receipt.relative_to(p)),
resource_scope="Current completed capped runner groups empty per receipts; standalone displays lack group/native UI telemetry; historical interrupted r3 group evidence absent",
files_inventory_method="Known copied-input filenames plus explicitly enumerated own absolute directories, no recursion")
write("audit/COMPLETED-RECEIPT-INVENTORY.json",json.dumps(inventory,indent=1)+"\n")
paths.add(p/"audit/COMPLETED-RECEIPT-INVENTORY.json")
hashes={str(f.relative_to(p)):sha(f) for f in sorted(paths) if str(f.relative_to(p)) not in exclude}
manifest=dict(sha256=hashes,file_count=len(hashes),exact_terminal_noncircular_self_exclusions=exclude,
scope="All copied inputs/helpers/pins/plans/current sources/build oleans/logs/receipts/audits/paper/renders/isolated controls/extracted source+build discovered by known copied filenames and explicit own directory enumeration",
status="FULL_ENDPOINT_REPLAYED_UNACCEPTED",credit=0,campaign=55,target=60,previous=39)
write("SHA256-MANIFEST.json",json.dumps(manifest,indent=1)+"\n")
for rel,h in hashes.items():assert sha(p/rel)==h,rel
print("SEALED",len(hashes),"FILES",len(all_receipts),"COMPLETED RECEIPTS", "SELF_EXCLUSIONS",exclude)
