from pathlib import Path
import json,hashlib,re,subprocess,sys,os,zipfile
L=Path(__file__).resolve().parent
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def revision(p):
 g=p/'.git'
 if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  r=h[5:];f=g/r
  h=f.read_text().strip() if f.exists() else next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+r))
 return h
def checkpins():
 manifest=json.loads((L/'administrative/lake-manifest.json').read_text())
 assert len(manifest['packages'])==9
 pins=[]
 for p in manifest['packages']:
  path=P/'.lake/packages'/p['name'];actual=revision(path);assert actual==p['rev'],p
  pins.append(dict(name=p['name'],revision=actual,path=str(path)))
 assert next(p['revision'] for p in pins if p['name']=='mathlib')=='d13f23b723b8a846827a245b89c10fc7d3f11612'
 assert sha(P/'lake-manifest.json')==sha(L/'administrative/lake-manifest.json')
 return pins
if sys.argv[1]=='audit':
 logs=list(L.glob('attempt-*.log'))
 inv=next(p.read_text() for p in reversed(sorted(logs)) if 'OWN_DECL ' in p.read_text())
 names=sorted(re.findall(r'^OWN_DECL (\S+)$',inv,re.M))
 safety=dict(re.findall(r'^OWN_SAFETY (\S+) (true|false)$',inv,re.M))
 assert names and set(names)==set(safety) and all(v=='false' for v in safety.values())
 (L/'owned-declarations.json').write_text(json.dumps(names,indent=2)+'\n')
 (L/'Audit.lean').write_text('''import Literal
import Lean
set_option pp.privateNames true
open Lean Elab Command in
elab "#audit_all" : command => do
 let env ← getEnv
 for (name, _) in env.constants do
  if let some idx := env.getModuleIdxFor? name then
   if env.header.moduleNames[idx.toNat]! == `Literal then
    elabCommand (← `(command| #check $(mkIdent name)))
    elabCommand (← `(command| #print axioms $(mkIdent name)))
#audit_all
''')
 (L/'pins.json').write_text(json.dumps(checkpins(),indent=2)+'\n')
elif sys.argv[1]=='pack':
 names=json.loads((L/'owned-declarations.json').read_text())
 audit=next(p.read_text() for p in reversed(sorted(L.glob('attempt-*.log'))) if 'depends on axioms' in p.read_text())
 ax={n:re.findall(r'[\w.]+',a) for n,a in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",audit,re.M)}
 empty=re.findall(r"^'([^']+)' does not depend on any axioms$",audit,re.M)
 assert set(names)==set(ax)|set(empty)
 assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in ax.values())
 (L/'audit.json').write_text(json.dumps(dict(status='PASS',declarations=[dict(name=n,axioms=ax.get(n,[]),isUnsafe=False) for n in names],scope='every actual declaration originating in Literal, including generated declarations; actual #check types and kernel axiom closure'),indent=2)+'\n')
 files=['Literal.lean','Inventory.lean','Audit.lean','runner.py','package.py','replay.py','RUN.md','owned-declarations.json','pins.json','administrative/lake-manifest.json']
 (L/'archive-files.json').write_text(json.dumps({f:sha(L/f) for f in files},indent=2)+'\n')
 with zipfile.ZipFile(L/'source-only.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
  for f in files+['archive-files.json']:
   info=zipfile.ZipInfo(f,date_time=(2026,10,30,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16;z.writestr(info,(L/f).read_bytes())
 for p in L.glob('*.olean'):p.unlink()
 print('source-only archive',sha(L/'source-only.zip'),'declarations',len(names))
