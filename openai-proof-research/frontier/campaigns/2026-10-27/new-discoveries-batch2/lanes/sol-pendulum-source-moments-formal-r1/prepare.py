import pathlib,json,hashlib
R=pathlib.Path(__file__).resolve().parent
old=R.parent/'sol-renyi-deficit-source-formal-r2'
s=(old/'formal/FullAudit.lean').read_text()
start=s.index('import all Pointwise');end=s.index('import Lean')
s=s[:start]+''.join('import all '+m+'\n' for m in ['Defs','Substitution','Moments','Source'])+s[end:]
start=s.index('  let mods :=');end=s.index('\n',start)
s=s[:start]+'  let mods := #[`Defs, `Substitution, `Moments, `Source]'+s[end:]
(R/'formal/FullAudit.lean').write_text(s)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
records=[]
for p in (R/'inputs').iterdir():
 original=R.parent/p.name.replace('--','/')
 records.append({'copy':str(p.relative_to(R)),'original':str(original),'sha256':sha(p)})
for n in ['guard.py','replay_guard.py','helper_guard.py','pins.json']:
 records.append({'copy':n,'original':str(old/n),'sha256':sha(R/n)})
(R/'input-records.json').write_text(json.dumps(records,indent=2)+'\n')
