import pathlib,json,collections,subprocess,sys
p=pathlib.Path.cwd()
log=(p/"logs/1794124865773641963_metadata_tool_closure.log").read_text()
ns=[json.loads(x[5:]) for x in log.splitlines() if x.startswith("NODE ")]
roots=json.loads(next(x[6:] for x in log.splitlines() if x.startswith("ROOTS ")))
def save(f,d):subprocess.run([sys.executable,"-I","-B",str(p/"write_lane.py"),f],input=json.dumps(d,indent=2),text=True,check=True)
save("audit/TOOL-METADATA.json",{"roots":roots,"nodes":ns})
summary={}
for s in ["production","auxiliary"]:
 a=[n for n in ns if n["scope"]==s]
 summary[s]={"roots":len(roots[s]),"closure":len(a),"kinds":dict(collections.Counter(n["kind"] for n in a)),"unsafe_partial":[n["name"] for n in a if n["unsafe"] or n["partial"]],"axioms":[n["name"] for n in a if n["kind"]=="axiom"],"origin_root_counts":dict(collections.Counter(n["origin"] for n in a if n["name"] in roots[s]))}
save("audit/TOOL-METADATA-SUMMARY.json",summary)
print(json.dumps(summary,indent=2))

