import pathlib,json,hashlib,subprocess,sys
p=pathlib.Path.cwd()
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
review=json.loads((p/"review.json").read_text())["326555"]
assert review["credit"]==0 and len(review["source_body_table"])==39
assert all(r["personal_review"]=="r6 full source body read" for r in review["source_body_table"])
replay=json.loads((p/"results/FRESH-REPLAY.json").read_text())
assert replay["strict"]==replay["checker"]==39
for m,h in replay["sources"].items():assert sha(p/"src"/(m+".lean"))==h
for m,h in replay["postchecker_oleans"].items():assert sha(p/"build"/(m+".olean"))==h
rs=[]
for f in sorted((p/"receipt").glob("*.json")):
 d=json.loads(f.read_text());assert not d["group_members_left"]
 log=pathlib.Path(d["log"]);assert log.is_relative_to(p)
 assert sha(log)==d["log_sha256"]
 rs.append({"path":str(f.relative_to(p)),"sha256":sha(f),"label":d["label"],"exit":d["exit"],"guard":d["guard"],"group_members_left":d["group_members_left"],"limits":d["limits"]})
d={"receipts":rs,"all_completed_groups_empty":True,"failed_attempts_retained":True,"source_olean_posthashes_valid":True,"metadata_auditor_sources":{str(f.relative_to(p)):sha(f) for f in (p/"src/audit").glob("*.lean")},"metadata_auditor_oleans":{str(f.relative_to(p)):sha(f) for f in (p/"build/audit").glob("*.olean")},"source_body_coverage_sha256":sha(p/"results/SOURCE-BODY-COVERAGE.json"),"review_sha256":sha(p/"review.json"),"report_sha256":sha(p/"FINAL-REVIEW.md")}
subprocess.run([sys.executable,"-I","-B",str(p/"write_lane.py"),"audit/COMPLETED-RECEIPTS.json"],input=json.dumps(d,indent=2),text=True,check=True)
print("POSTFLIGHT",len(rs),"completed receipts", "failed",[(x["label"],x["exit"]) for x in rs if x["exit"]])

