from pathlib import Path
import json,hashlib,shutil
P=Path(__file__).resolve().parents[1];B=P.parent
rows=[]
for f in ['replay-result.json','registry-refresh.json']:
 s=B/'rainbow-parent-final-r1'/f
 if s.exists():
  rows.append({'path':str(s.relative_to(B)),'sha256':hashlib.sha256(s.read_bytes()).hexdigest(),'bytes':s.stat().st_size});d=P/'evidence/root'/f;d.parent.mkdir(exist_ok=True);shutil.copyfile(s,d)
(P/'root-input-before.json').write_text(json.dumps(rows,indent=2)+'\n')
p=P/'manuscript.md';s=p.read_text();s=s.replace('The separately supplied root replay status is appended below before final packaging.','The separate root replay-result.json (4 November 2026 UTC) reports PASS: root’s own driver built and explicitly checked 21/21 modules including Audit, with peak RSS 3.46 GB, and independently rechecked the coloring certificates. Root’s metadata audit found 168 declarations and no prohibited flags; the literal endpoint has only the three allowed axioms. This is a supplied root receipt, not a replay performed by this manuscript lane. The accompanying registry refresh records bounded complete-subtree path screening and unrelated rainbow-connector hits. Root paper review and acceptance remain outstanding.');p.write_text(s)
