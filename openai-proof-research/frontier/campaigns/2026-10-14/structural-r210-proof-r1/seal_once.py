"""One-time seal for this completed independent review packet only."""
from pathlib import Path
import hashlib,json,os,runpy,stat

root=Path(__file__).resolve().parent
packet=root/"packet"
manifest=root/"MANIFEST.json"
if manifest.exists(): raise RuntimeError("Refusing to reseal an existing review manifest")
verify=runpy.run_path(str(root/"verify_packet.py"))
for folder,dirs,files in os.walk(packet):
    directory=Path(folder)
    rel=directory.relative_to(packet)
    protected=bool(rel.parts and rel.parts[0]=="private")
    directory.chmod(0o700 if protected else 0o755)
    for name in files:
        p=directory/name
        if p.is_symlink(): raise RuntimeError("Symbolic link in review selection")
        p.chmod(0o600 if protected else 0o644)
entries=[]
for name,data in sorted(verify["inventory"](packet).items()):
    protected=name=="private" or name.startswith("private/")
    rights="Private/local; copied bodies and metadata retain original rights; no redistribution" if protected else "Original independent review artifact; local handoff"
    entries.append(dict(path=name,rights=rights,**data))
final_hash=verify["digest"](packet/"FINAL.md")
manifest.write_text(json.dumps({"format":verify["FORMAT"],"final":"FINAL.md","scope":"Entire unchanged Structural210 frozen statement and submitted proof; correctness only","entries":entries},indent=2)+"\n")
manifest.chmod(0o644)
manifest_hash=verify["digest"](manifest)
report_template=Path(root/"report_template.txt").read_text()
report=report_template.replace("@FINAL_HASH@",final_hash).replace("@MANIFEST_HASH@",manifest_hash)
(root/"REPORT.md").write_text(report)
(root/"REPORT.md").chmod(0o644)
report_hash=verify["digest"](root/"REPORT.md")
for name,value in [("FINAL",final_hash),("MANIFEST",manifest_hash),("REPORT",report_hash)]:
    (root/(name+".sha256")).write_text(value+"\n")
result=verify["verify"](packet,manifest,manifest_hash,final_hash,root/"REPORT.md",report_hash)
(root/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
