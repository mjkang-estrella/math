"""Tiny synthetic checks; mutate only this review root's synthetic fixtures."""
import hashlib
import json
from pathlib import Path
import runpy
import shutil
import sys

root=Path(__file__).resolve().parents[2]
module=runpy.run_path(str(root/"verify_packet.py"))
verify,inventory,digest=module["verify"],module["inventory"],module["digest"]
base=root/"synthetic-controls"
if base.exists():
    raise RuntimeError("Do not rerun controls over existing fixtures")
packet=base/"packet"
(packet/"private").mkdir(parents=True,mode=0o700)
(packet/"private").chmod(0o700)
(packet/"FINAL.md").write_text("Synthetic final only.\n")
(packet/"private/sample.txt").write_text("Synthetic protected bytes.\n")
(packet/"private/sample.txt").chmod(0o600)
report=base/"REPORT.md"
report.write_text("Synthetic outside report.\n")
report.chmod(0o644)
manifest=base/"MANIFEST.json"
manifest.write_text(json.dumps({"format":module["FORMAT"],"final":"FINAL.md","entries":[dict(path=name,**data) for name,data in sorted(inventory(packet).items())]},indent=2)+"\n")
args=[packet,manifest,digest(manifest),digest(packet/"FINAL.md"),report,digest(report)]
results=[]
def expect(label,accepted,arguments=None):
    try:
        verify(*(arguments or args))
        observed=True;reason="accepted"
    except ValueError as error:
        observed=False;reason=str(error)
    if observed!=accepted: raise AssertionError(label)
    results.append({"case":label,"expected_accept":accepted,"observed_accept":observed,"result":reason})
expect("intact selection",True)
sample=packet/"private/sample.txt";original=sample.read_bytes()
sample.write_bytes(original+b"changed\n");expect("modified protected bytes",False);sample.write_bytes(original)
extra=packet/"extra.txt";extra.write_text("extra\n");expect("extra selected file",False);extra.unlink()
sample.chmod(0o644);expect("protected mode change",False);sample.chmod(0o600)
sample.unlink();expect("missing selected file",False);sample.write_bytes(original);sample.chmod(0o600)
wrong=list(args);wrong[3]="0"*64;expect("wrong detached FINAL anchor",False,wrong)
expect("restored selection",True)
(root/"packet/private/artifact-controls.json").write_text(json.dumps({"synthetic_only":True,"author_material_untouched":True,"cases":results},indent=2)+"\n")
print(json.dumps(results,indent=2))
