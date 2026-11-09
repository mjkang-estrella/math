"""Create this owned exact packet once. Does not run or grant mathematical gates."""
from pathlib import Path, PurePosixPath
import hashlib,json,os,stat
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r214').resolve()
OUTSIDE={'MANIFEST.json','REPORT.md','ANCHORS.json','verification.json'}
assert not any((R/n).exists() for n in ['MANIFEST.json','SELECTION.json','ANCHORS.json','verification.json']), 'already selected/sealed; do not reseal'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for a in json.loads((R/'private/source-authentication.json').read_bytes()):
 b=(R/a['local']).read_bytes()
 assert len(b)==a['bytes'] and hashlib.sha256(b).hexdigest()==a['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==a['git_blob']
files=[]
for base,dirs,names in os.walk(R,followlinks=False):
 rel=Path(base).relative_to(R).as_posix()
 if rel=='.':dirs[:]=[d for d in dirs if d!='controls']
 for d in dirs:assert not (Path(base)/d).is_symlink()
 for n in names:
  p=Path(base)/n;assert stat.S_ISREG(p.lstat().st_mode) and not p.is_symlink()
  q=p.relative_to(R).as_posix()
  if q not in OUTSIDE:files.append(q)
files=sorted(files+['SELECTION.json']);assert len(files)==len(set(files))
selection={'schema':'r214-selection-v1','files':files,'outside_files':sorted(OUTSIDE),'outside_directories':['controls'],'semantics':'Exact selected files; acquisition and authentication are not semantic reading. No inherited manifest.'}
with (R/'SELECTION.json').open('x') as f:f.write(json.dumps(selection,indent=2)+'\n')
entries=[]
for name in files:
 p=R/name;private=name.startswith('private/') or name in {'GUARDS.json','SESSION.md','SELECTION.json'}
 p.chmod(0o400 if private else 0o444)
 rights='private-original-rights' if name.startswith('private/') else ('private-task-metadata' if private else 'original-local')
 entries.append({'path':name,'bytes':p.stat().st_size,'sha256':sha(p),'mode':'0400' if private else '0444','rights':rights})
dirs=sorted({p.as_posix() for name in files for p in PurePosixPath(name).parents if p.as_posix()!='.'})
R.chmod(0o700)
for p in R.rglob('*'):
 if p.is_dir():p.chmod(0o700)
(R/'REPORT.md').chmod(0o444)
manifest={'schema':'r214-exact-selection-v1','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','outcome':'PREFREEZE/no nominee; no grade or count','files':entries,'directories':[{'path':d,'mode':'0700'} for d in dirs]}
with (R/'MANIFEST.json').open('x') as f:f.write(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n')
(R/'MANIFEST.json').chmod(0o400)
anchors={'FINAL.md':sha(R/'FINAL.md'),'MANIFEST.json':sha(R/'MANIFEST.json'),'REPORT.md':sha(R/'REPORT.md')}
with (R/'ANCHORS.json').open('x') as f:f.write(json.dumps(anchors,indent=2)+'\n')
(R/'ANCHORS.json').chmod(0o400)
print(json.dumps({'selected_files':len(entries),'selected_bytes':sum(e['bytes'] for e in entries),'anchors':anchors},indent=2))
