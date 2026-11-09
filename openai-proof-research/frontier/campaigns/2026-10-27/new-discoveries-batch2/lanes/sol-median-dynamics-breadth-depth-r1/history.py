from pathlib import Path
import json,hashlib,shutil,re
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((L/'freeze.json').read_text());reports=[]
for p in sorted(L.parent.glob('*r21[3-9]/SCOUTING.md'))+sorted(L.parent.glob('*r220/SCOUTING.md')):
 q=L/'frozen'/(p.parent.name+'--SCOUTING.md');before=h(p);shutil.copyfile(p,q);assert before==h(q)==h(p)
 records.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=before,administrative=False));reports.append(q)
(L/'freeze.json').write_text(json.dumps(records,indent=2))
reports.append(L/'frozen'/'r221--SCOUTING.md')
ids=[p.stem for p in (L/'frozen').glob('2610*.pdf')]
terms=['median','majority','Fasi','Higham','diversity','Leinster','unit width','fence','orthogonal','phase-type','Kelly','Condorcet','discrete monotonicity','longest increasing','Turán','random trees','singularity']
out={}
for term in ids+terms:
 matches=[]
 for p in reports+[L/'frozen'/'pinned-CONTENTS.md']:
  lines=p.read_text().splitlines()
  for i,line in enumerate(lines):
   if term.lower() in line.lower():matches.append(dict(file=str(p.relative_to(L)),line=i+1,text=line[:1000]))
 out[term]=matches
(L/'history-screen.json').write_text(json.dumps(out,indent=2));print({k:len(v) for k,v in out.items()})
# Read administrative snapshots in full, retain compact titles and ledger state.
a=json.loads((L/'administrative'/'ledger.json').read_text());b=json.loads((L/'administrative'/'prior-campaign-context.json').read_text())
(L/'administrative-read.json').write_text(json.dumps(dict(accepted_count=a['accepted_count'],total_accepted_count=a['total_accepted_count'],next_global_outcome_number=a['next_global_outcome_number'],ledger_titles=[x.get('title') for x in a['accepted']],prior_titles=[x.get('title') for x in b['accepted']]),indent=2))
