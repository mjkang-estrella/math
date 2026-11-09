from research import *
import subprocess
j=json.loads((ROOT/'frontier/campaigns/2026-10-14/tasks.json').read_text())
active=[]
for t in j['tasks']:
 s=str(t.get('status','')).lower()
 if any(x in s for x in ['running','pending','queued','dispatch','in_progress','working']) and not any(x in s for x in ['completed','failed','cancel']):
  o=t.get('output');
  if isinstance(o,str):active.append(pathlib.Path(o).name)
# Review/formal/release bodies excluded wholesale, including copied directory components.
corpus={'.git','node_modules','.venv','venv','__pycache__','preprints','primary','rendered','renders','controls','tamper-controls','context','upstream','source','downloads'}
def skip(n):
 return forbidden(n) or n in active or n=='fresh-structural-discovery-r141' or n in corpus or any(fnmatch.fnmatch(n.lower(),p) for p in ['*review*','*contribution*','*formal*','*manuscript*','*release*','*publication*','*-proof-r*'])
paths=[];pruned=set()
for top in ['frontier','experiments','proposals','scouts','notes','iterations','findings']:
 if not (ROOT/top).exists():continue
 for d,dirs,files in os.walk(ROOT/top,followlinks=False):
  keep=[]
  for n in dirs:
   if skip(n):pruned.add(n)
   elif not (pathlib.Path(d)/n).is_symlink():keep.append(n)
  dirs[:]=keep
  for f in files:
   if skip(f):continue
   p=pathlib.Path(d)/f
   if not p.is_symlink():paths.append(str(p.relative_to(ROOT)))
# Pass explicit files: hidden/ignored/JSON/large included, no size cutoff.
pattern=r'Shareshian|chromatic.quasisymmetric|elementary.unimod|e.unimodal|theta.section|Lefschetz.*(graph|chromatic)|T169|I169|Foulkes'
hits=[];errors=[]
for i in range(0,len(paths),400):
 r=subprocess.run(['rg','-a','-i','-l','--no-messages',pattern,'--',*paths[i:i+400]],cwd=ROOT,capture_output=True,text=True)
 if r.returncode not in (0,1):errors.append(r.stderr)
 hits+=r.stdout.splitlines()
save('search/history-search.json',dict(utc=now(),pattern=pattern,files_searched=len(paths),hits=hits,active_component_observations=active,pruned_components=sorted(pruned),errors=errors,limits='Navigation only; all review/contribution/formal/manuscript/release roots pruned, including completed. No blanket private/work/frozen exclusion. Corpus components pruned. No claim of exhaustive semantic clearance.'))
print('scanned',len(paths),'hitfiles',len(hits),'errors',len(errors));print('active',active)
for p in hits:
 if not any(x in p.split('/') for x in ['inputs','snapshots','frozen','recovery-context','copied-originals']):print(p)
