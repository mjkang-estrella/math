from pathlib import Path
import json,hashlib,subprocess,sys,os,stat
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r125');C=R/'private/copied-controls';C.mkdir(exist_ok=False)
(C/'payload').mkdir();sources=[R/'notes/feasibility.md',R/'private/source/02-finite-fields.tex']
members=[]
for i,p in enumerate(sources):
 b=p.read_bytes();q=C/'payload'/f'member{i}.txt';q.write_bytes(b)
 members.append({'original':str(p.relative_to(R)),'selected_copy':str(q.relative_to(C)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(C/'verify.py').write_bytes((R/'verify.py').read_bytes())
(C/'FINAL.md').write_text('Copied control only. No mathematical outcome.\n');(C/'REPORT.md').write_text('Two selected members and copied verifier; independent membership, no inherited source manifest.\n')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snap():
 x=[]
 for dp,ds,fs in os.walk(C):
  for name in sorted(ds):x.append((str((Path(dp)/name).relative_to(C)),'dir'))
  for name in sorted(fs):
   p=Path(dp)/name;x.append((str(p.relative_to(C)),len(p.read_bytes()),digest(p)))
 return sorted(x)
files={}
for p in [C/'verify.py',C/'payload/member0.txt',C/'payload/member1.txt']:
 files[str(p.relative_to(C))]={'size':p.stat().st_size,'sha256':digest(p)}
(C/'MANIFEST.json').write_text(json.dumps({'schema':'r125-exact-v1','outside_payload_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],'files':dict(sorted(files.items())),'directories':['payload']},indent=2)+'\n')
anchors=[digest(C/x) for x in ['FINAL.md','MANIFEST.json','REPORT.md']];out=[]
def run(name,expected,aa=None):
 before=snap();p=subprocess.run([sys.executable,'-B',str(C/'verify.py'),str(C),*(aa or anchors)],capture_output=True,text=True,timeout=15)
 after=snap();assert before==after,(name,'verifier modified fixture')
 assert (p.returncode==0)==expected,(name,p.stdout,p.stderr)
 out.append({'case':name,'accepted':p.returncode==0,'expected':expected,'read_only_snapshot_equal':True,'stdout':p.stdout.strip()})
run('baseline',True)
p=C/'payload/member0.txt';b=p.read_bytes();p.write_bytes(b+b'changed\n');run('changed payload',False);p.write_bytes(b)
p=C/'payload/member1.txt';b=p.read_bytes();p.unlink();run('missing payload',False);p.write_bytes(b)
p=C/'.hidden-extra';p.write_text('extra');run('extra hidden member',False);p.unlink()
p=C/'empty-extra';p.mkdir();run('extra empty directory',False);p.rmdir()
bad=anchors[:];bad[1]='0'*64;run('wrong detached manifest anchor',False,bad)
run('restored baseline',True)
for p,m in zip(sources,members):assert digest(p)==m['sha256']
(R/'private/control-results.json').write_text(json.dumps({'fixture':'private/copied-controls','membership':members,'detached_fixture_anchors':dict(zip(['FINAL','MANIFEST','REPORT'],anchors)),'cases':out,'originals_unchanged':True,'limits':'Artifact controls only; no mathematical gate.'},indent=2)+'\n')
print('Seven copied controls matched; all calls read-only; both originals unchanged.')
