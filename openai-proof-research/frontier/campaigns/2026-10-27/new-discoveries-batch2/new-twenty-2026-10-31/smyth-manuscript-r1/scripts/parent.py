from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parent.parent;P=R.parent/'smyth-parent-final-r1';out={}
for name in ['replay-result.json','registry-refresh.json']:
 f=P/name;b=f.read_bytes();out[str(f)]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
 d=R/'evidence/smyth-parent-final-r1'/name;d.parent.mkdir(exist_ok=True);d.write_bytes(b)
(R/'inputs-parent-before.json').write_text(json.dumps(out,indent=2)+'\n')
p=R/'scripts/paper.py';s=p.read_text().replace("Smyth's\\ninjection", "Smyth's\ninjection")
s=s.replace("s=s.replace('STATUS_PARENT','pending at the manuscript snapshot')", "s=s.replace('STATUS_PARENT','reported complete in the supplied root receipts')")
s=s.replace("Human review of statement fidelity,", "The root replay reports success for every packet module and its checker.\nThe refreshed registry result is a path screen with selected header reads,\nnot an exhaustive proof-body search. Human review of statement fidelity,")
p.write_text(s)
