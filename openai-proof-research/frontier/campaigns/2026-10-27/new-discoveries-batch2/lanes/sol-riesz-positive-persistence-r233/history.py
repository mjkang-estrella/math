from research import L,B,freeze
import subprocess,pathlib,json
patterns='Riesz|Grabner|Bilyk|Hilbert.*quotient|nested convex|cosectional|involution|Fubini|sponge|energetic points|center of distances|Steiner.*random|random.*Steiner'
roots=[B,B.parent.parent/'2026-10-26/new-discoveries']
args=['rg','-l','-i',patterns]+[str(p) for p in roots if p.exists()]+['-g','SUMMARY.md','-g','discovery.md','-g','discovery.json','-g','*aliases*.json']
paths=subprocess.run(args,capture_output=True,text=True).stdout.splitlines()
out=[]
for p in paths:
 p=pathlib.Path(p)
 if not any(len(p.relative_to(r).parts)==3 and p.relative_to(r).parts[0]=='lanes' for r in roots if r in p.parents):continue
 if L in p.parents or 'copies' in p.parts or 'frozen' in p.parts or p.stat().st_size>100000:continue
 q=freeze(p);s=q.read_text(errors='replace');out.append({'original':str(p),'frozen':str(q),'text':s[:18000]})
(L/'breadth-history.json').write_text(json.dumps(out,indent=2));print({'canonical_reports':len(out)})
