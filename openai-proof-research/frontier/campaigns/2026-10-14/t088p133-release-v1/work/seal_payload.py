from pathlib import Path
import hashlib,json,stat
r=Path(__file__).resolve().parents[1];s=r/'public-source'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
a=json.loads((s/'assembly-map.json').read_text())
generated=sorted(p.relative_to(s).as_posix() for p in s.rglob('*') if p.is_file() and p.relative_to(s).as_posix() not in a['copied'] and p.name not in ['assembly-map.json','MANIFEST.json'])
a['generated']={p:{'sha256':sha(s/p),'bytes':(s/p).stat().st_size,'role':'new release routing, documentation or declared tool-input metadata'} for p in generated};a['self_hash']='assembly-map.json is bound by MANIFEST.json, avoiding a self-hash cycle.'
(s/'assembly-map.json').write_text(json.dumps(a,indent=2,sort_keys=True)+'\n')
files={};dirs={}
for p in sorted(s.rglob('*')):
 assert not p.is_symlink()
 rel=p.relative_to(s).as_posix()
 if p.is_dir():p.chmod(0o755);dirs[rel]=0o755
 elif rel!='MANIFEST.json':p.chmod(0o444);files[rel]={'bytes':p.stat().st_size,'mode':0o444,'sha256':sha(p)}
m={'schema':'T088P133-portable-local-release-manifest-v1','files':files,'directories':dirs,'coverage':'Exact entire archive; MANIFEST.json separately externally anchored; no private/local work or dependency bodies.'}
(s/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');(s/'MANIFEST.json').chmod(0o444);s.chmod(0o755)
(r/'MANIFEST.json').write_bytes((s/'MANIFEST.json').read_bytes());print(json.dumps({'payload_files':len(files),'archive_files':len(files)+1,'directories':len(dirs),'zip_entries':len(files)+1+len(dirs),'manifest_sha256':sha(s/'MANIFEST.json')}))
