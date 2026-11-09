from pathlib import Path
import shutil,json,hashlib,zipfile,stat
r=Path(__file__).resolve().parent.parent;b=r.parent
copied=[]
def cp(p,t):
 t=r/t;t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,t)
 copied.append({'source':str(p.resolve()),'destination':str(t.relative_to(r)),'sha256':hashlib.sha256(t.read_bytes()).hexdigest()})
for lane,names in {
 'middle-formal-r1':['SUMMARY.md','results.json','STATEMENT-CORRESPONDENCE.md','PROOF.md','REPRODUCE.md','audit.jsonl','regression.json'],
 'middle-fidelity-r1':['REVIEW.md','review.json','audit-summary.json','sanity.json','Sanity.lean'],
 'middle-review-r1':['REVIEW.md','review.json'],
 'middle-parent-final-r1':['replay-result.json','registry-refresh.json','root-replay.out'],
 'expanded-corpus-r139':['work355217/PROOF.md','raw/355217.jsonl','results.json']}.items():
 for n in names: cp(b/lane/n,Path('evidence')/lane/n)
for lane,dirs in {'middle-review-r1':['scripts','data','logs','downloads'],'middle-fidelity-r1':['scripts','logs'],'middle-parent-final-r1':['registries','rootcheck'],'expanded-corpus-r139':['sources']}.items():
 for d in dirs:
  for p in sorted((b/lane/d).rglob('*')):
   if p.is_file() and p.suffix not in ['.olean','.ilean','.c','.o']:cp(p,Path('evidence')/lane/p.relative_to(b/lane))
for p in (b/'expanded-corpus-r139/work355217').glob('*.py'):cp(p,Path('evidence/expanded-corpus-r139/work355217')/p.name)
cp(b/'expanded-corpus-r139/scripts/graphgen.py',Path('evidence/expanded-corpus-r139/scripts/graphgen.py'))
cp(b/'middle-root-ruling-r1.json',Path('evidence/middle-root-ruling-r1.json'))
cp(b/'middle-formal-r1/middle-source.zip',Path('middle-source.zip'))
expected='5a3e8ac8153651c55942d8f1288b50dd0c578b089c02d01c353b750b2c5bb62b'
assert hashlib.sha256((r/'middle-source.zip').read_bytes()).hexdigest()==expected
(r/'receipts/copied-inputs.json').write_text(json.dumps(copied,indent=2)+'\n')
