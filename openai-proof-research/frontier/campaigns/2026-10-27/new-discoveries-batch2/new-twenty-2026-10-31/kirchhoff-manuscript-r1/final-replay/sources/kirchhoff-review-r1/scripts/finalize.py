from pathlib import Path
import hashlib,json,re,datetime
D=Path(__file__).resolve().parents[1]
h=json.loads((D/'receipts/input-before.json').read_text());after={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in h}
(D/'receipts/input-after.json').write_text(json.dumps(after,indent=2));assert h==after
packet={}
for p in (D/'fresh/formal').glob('*.lean'):
 if p.name.startswith('Reviewer'):continue
 src= D.parent/'kirchhoff-formal-r2/formal'/p.name
 assert p.read_bytes()==src.read_bytes();packet[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
# Forbidden proof mechanisms: tokens, not the legitimate diagnostic command `#print axioms`.
for p in (D/'fresh/formal').glob('*.lean'):
 text=re.sub(r'"[^"\n]*"','""',p.read_text());assert not re.search(r'\b(sorry|admit|axiom|native_decide|ofReduceBool|implemented_by|extern)\b',text),p
rows=[];count=None
with (D/'logs/reviewer-audit.log').open() as f:
 for line in f:
  if line.startswith('DECL|'):rows.append(line.strip())
  if 'AUDITED_LOCAL_DECLARATIONS|' in line:count=int(line.split('|')[-1])
assert count==len(rows) and count>=176
assert all('|UNSAFE|false|PARTIAL|false|' in r for r in rows)
receipts=[]
for p in (D/'receipts').glob('*.json'):
 r=json.loads(p.read_text())
 if 'returncode' in r:receipts.append(dict(name=p.stem,**r))
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_files':len(h),'unchanged':h==after,'extracted_matches_author_formal':packet,'local_declaration_count':count,'declarations':rows,'peak_private_rss':max(r['peak_private_rss'] for r in receipts),'max_call_wall_seconds':max(r['wall_seconds'] for r in receipts),'guard_kills':[r for r in receipts if r['killed']],'allowed_axioms':['propext','Classical.choice','Quot.sound']}
(D/'receipts/verification-summary.json').write_text(json.dumps(r,indent=2));print({k:v for k,v in r.items() if k!='declarations'})
