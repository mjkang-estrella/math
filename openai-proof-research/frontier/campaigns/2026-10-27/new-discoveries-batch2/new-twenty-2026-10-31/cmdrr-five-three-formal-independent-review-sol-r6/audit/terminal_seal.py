import pathlib,json,hashlib,subprocess,sys
p=pathlib.Path.cwd()
active=sorted((p/"logs").glob("*_terminal_seal.log"))
assert len(active)==1
log=active[0];receipt=p/"receipt"/(log.stem+".json")
ex=["SHA256-MANIFEST.json",str(log.relative_to(p)),str(receipt.relative_to(p))]
files={}
for f in sorted(p.rglob("*")):
 assert not f.is_symlink(),str(f)
 if f.is_file() and str(f.relative_to(p)) not in ex:
  files[str(f.relative_to(p))]=hashlib.sha256(f.read_bytes()).hexdigest()
d={"scope":"All actual files recursively within this exact assigned lane only; no embedded original paths followed","files":files,"exact_terminal_noncircular_exclusions":ex,"exclusion_reason":"Manifest self-reference and active sealing runner log/receipt; no broad directory exclusions","frozen_after":json.loads((p/"frozen-after.json").read_text()),"credit":0,"campaign":55,"root_adjudication":"PENDING","all_prior_completed_groups_empty":True}
subprocess.run([sys.executable,"-I","-B",str(p/"write_lane.py"),"SHA256-MANIFEST.json"],input=json.dumps(d,indent=2),text=True,check=True)
print("MANIFEST_COUNT",len(files),"EXACT_EXCLUSIONS",json.dumps(ex))
print("FINAL_REVIEW_SHA256",files["FINAL-REVIEW.md"])
print("REVIEW_JSON_SHA256",files["review.json"])

