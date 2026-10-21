"""Bounded selected-copy controls; only writes inside r115/packet/private/controls."""
from pathlib import Path
import hashlib,json,shutil,subprocess,os,stat
R=Path.cwd()/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r115'; C=R/'packet/private/controls'; F=C/'fixture'
C.mkdir(exist_ok=True);F.mkdir(exist_ok=False)
selected=['packet/tools/verify.py','packet/notes/affine-reduction.md','packet/source-identities.json']
for n in selected:
 p=F/n;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(R/n,p)
(F/'FINAL.md').write_text('Disposable selected-copy control packet. Not an original archive.\n')
(F/'REPORT.md').write_text('Copies three actual r115 files only. Own manifest and anchors. Artifact control only.\n')
def snap(root):
 out={}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;st=p.lstat();r=p.relative_to(root).as_posix()
   if stat.S_ISLNK(st.st_mode):out[r]=['link',os.readlink(p)]
   elif stat.S_ISDIR(st.st_mode):out[r]=['dir']
   else:out[r]=['file',st.st_size,hashlib.sha256(p.read_bytes()).hexdigest(),st.st_nlink]
 return out
s=snap(F);env=['FINAL.md','MANIFEST.json','REPORT.md'];m={'format':'r115-exact-v1','outside_envelopes':env,'files':{k:{'bytes':v[1],'sha256':v[2]} for k,v in s.items() if v[0]=='file' and k not in env},'directories':sorted(k for k,v in s.items() if v[0]=='dir')}
(F/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
anchors=[hashlib.sha256((F/n).read_bytes()).hexdigest() for n in env];rows=[]
def test(name,ok,aa=None):
 before=snap(F);r=subprocess.run(['python','-I','-B',str(F/'packet/tools/verify.py'),str(F),*(aa or anchors)],capture_output=True,text=True,timeout=15)
 after=snap(F);assert before==after,name+' verifier wrote files';assert (r.returncode==0)==ok,(name,r.stdout,r.stderr)
 rows.append(dict(case=name,expected_accept=ok,returncode=r.returncode,stdout=r.stdout.strip(),stderr=r.stderr.strip(),whole_fixture_unchanged=True))
test('baseline',True)
p=F/'packet/notes/affine-reduction.md';b=p.read_bytes();p.write_bytes(b+b'\nmutation\n');test('modified payload',False);p.write_bytes(b)
p.unlink();test('missing payload',False);p.write_bytes(b)
p=F/'packet/.unexpected';p.write_text('extra');test('hidden extra',False);p.unlink()
p=F/'packet/empty-extra';p.mkdir();test('empty extra directory',False);p.rmdir()
test('wrong detached manifest anchor',False,[anchors[0],'0'*64,anchors[2]])
test('restored',True)
(C/'receipt.json').write_text(json.dumps(dict(scope='selected-copy controls, not whole final packet or old original archive',selected_from_r115=selected,fixture_envelope_anchors=dict(zip(env,anchors)),cases=rows),indent=2)+'\n')
print(json.dumps({'controls':len(rows),'all_expected':True,'all_invocations_read_only':True}))
