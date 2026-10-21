"""Small selection with its OWN manifest; never reuse an original's manifest."""
import hashlib,json,os,shutil,stat,subprocess,sys
from pathlib import Path
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
O=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r118/packet'
D=O/'private/controls';D.mkdir();(D/'payload').mkdir()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
items=[('code/verify.py','verify.py'),('notes/feasibility.md','feasibility.md'),('source-identities.json','source-identities.json')];mapping=[]
for src,dst in items:
 p=D/'payload'/dst;shutil.copyfile(O/src,p);mapping.append({'original':src,'original_sha256':h(O/src),'copy':'payload/'+dst,'copy_sha256':h(p)})
(D/'FINAL.md').write_text('Disposable three-file integrity selection. No mathematical claims.\n')
(D/'REPORT.md').write_text('Selection membership uses its own manifest, not an incoming manifest.\n')
files={str(p.relative_to(D)):{'size':p.stat().st_size,'sha256':h(p)} for p in (D/'payload').iterdir()}
(D/'MANIFEST.json').write_text(json.dumps({'schema':'r118-exact-v1','files':files,'directories':['payload']},sort_keys=True,indent=2)+'\n')
anchors={n:h(D/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snapshot():
 rows=[]
 for d,ds,fs in os.walk(D):
  for n in ['.']+fs:
   p=Path(d) if n=='.' else Path(d)/n;s=p.lstat();rows.append([str(p.relative_to(D)),stat.S_IMODE(s.st_mode),s.st_nlink,s.st_size if p.is_file() else None,h(p) if p.is_file() else None])
 return sorted(rows)
def run(name,want,override=None):
 a=dict(anchors);a.update(override or {});before=snapshot();r=subprocess.run([sys.executable,str(O/'code/verify.py'),str(D),'--final',a['FINAL.md'],'--manifest',a['MANIFEST.json'],'--report',a['REPORT.md']],cwd=ROOT,text=True,capture_output=True);after=snapshot();ok=r.returncode==0
 assert ok==want and before==after,(name,r.stdout,r.stderr)
 return {'name':name,'accepted':ok,'expected_acceptance':want,'read_only_snapshot_equal':before==after,'output':(r.stdout+r.stderr).strip()}
rs=[run('baseline',True)];p=D/'payload/feasibility.md';b=p.read_bytes();p.write_bytes(b+b'changed\n');rs.append(run('altered payload',False));p.write_bytes(b);p.unlink();rs.append(run('missing payload',False));p.write_bytes(b)
p=D/'.extra';p.write_text('extra');rs.append(run('hidden extra',False));p.unlink();p=D/'empty-extra';p.mkdir();rs.append(run('empty extra directory',False));p.rmdir();rs.append(run('wrong detached manifest anchor',False,{'MANIFEST.json':'0'*64}));rs.append(run('restored',True))
for row in mapping:assert h(O/row['original'])==row['original_sha256'] and h(D/row['copy'])==row['copy_sha256']
(O/'control-results.json').write_text(json.dumps({'selection_mapping':mapping,'anchors':anchors,'controls':rs,'originals_unchanged':True,'limits':'Integrity only; no mathematical gate. No permissions/mode binding by manifest.'},indent=2)+'\n')
print('Seven expected outcomes; seven read-only snapshots; selected originals unchanged.')
