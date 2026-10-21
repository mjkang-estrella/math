"""Proportionate selected-copy controls; never inherits an original manifest."""
from pathlib import Path
import runpy,json,hashlib,subprocess,shutil,os,stat
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r150'
D=R/'private/controls';F=D/'selected-copy';assert not D.exists();F.mkdir(parents=True)
selected=['notes/02-integrated-reduction-and-gap.md','code/core_diagnostic.py','code/verify.py','private/source131/build/sections/setup.tex']
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
originals={p:h(R/p) for p in selected}
for name in selected:
 t=F/name;t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(R/name,t)
seal=runpy.run_path(str(R/'code/seal.py'))['seal']
anchors=seal(F,'Selected-copy FINAL; integrity only.\n','Selected-copy REPORT. Fresh manifest for four selected files; not the original packet.\n')
def snapshot():
 out={}
 for b,ds,fs in os.walk(F):
  for name in ['']+fs:
   p=Path(b)/name;s=p.lstat();out[p.relative_to(F).as_posix()]=[stat.S_IMODE(s.st_mode),s.st_nlink,h(p) if p.is_file() else 'DIR']
 return out
results=[]
def check(name,want,override=None):
 before=snapshot();a=dict(anchors);a.update(override or {})
 cmd=['python','-B',str(R/'code/verify.py'),str(F),'--final',a['FINAL.md'],'--manifest',a['MANIFEST.json'],'--report',a['REPORT.md']]
 t=subprocess.run(cmd,cwd=P,capture_output=True,text=True)
 assert (t.returncode==0)==want,(name,t.stdout,t.stderr)
 assert before==snapshot(),'verifier mutated fixture'
 results.append({'name':name,'accepted':t.returncode==0,'read_only_snapshot_unchanged':True,'output':t.stdout.strip()})
check('baseline',True)
p=F/selected[0];old=p.read_bytes();p.write_bytes(old+b'changed\n');check('changed payload',False);p.write_bytes(old)
p.unlink();check('missing payload',False);p.write_bytes(old)
p=F/'.extra';p.write_text('x');check('hidden extra',False);p.unlink()
p=F/'empty-extra';p.mkdir();check('empty extra directory',False);p.rmdir()
check('wrong detached REPORT anchor',False,{'REPORT.md':'0'*64})
check('restored',True)
assert originals=={p:h(R/p) for p in selected}
incoming=json.loads((R/'private/incoming-originals.json').read_text())['records']
stable=[{'path':x['path'],'matches_late_snapshot':h(P/x['path'])==x['sha256']} for x in incoming]
assert all(x['matches_late_snapshot'] for x in stable)
(D/'results.json').write_text(json.dumps({'selected_copy_membership':'fresh exact reduced manifest; no inherited manifest','selected_original_hashes':originals,'detached_copy_anchors':anchors,'controls':results,'incoming_current_originals':stable},indent=2)+'\n')
print(json.dumps({'controls':len(results),'original_selected_files_unchanged':len(originals),'incoming_late_snapshots_stable':len(stable)},indent=2))
