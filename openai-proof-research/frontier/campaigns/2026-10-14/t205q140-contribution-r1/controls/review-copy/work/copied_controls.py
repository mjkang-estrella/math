# MIT. After sealing, mutates only a fresh controls/review-copy fixture.
from pathlib import Path
import json,hashlib,shutil,subprocess,sys,datetime
R=Path(__file__).resolve().parents[1];C=R/'controls/review-copy';assert not C.exists()
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
names=['MANIFEST.json','outsideREPORT.md','FINAL.json'];anchors={n:h(R/n) for n in names}
def command(root):return [sys.executable,'-B',str(root/'packet/public/verify.py'),'--root',str(root),'--manifest-sha256',anchors[names[0]],'--report-sha256',anchors[names[1]],'--final-sha256',anchors[names[2]]]
def run(root,ok=True,args=None):
 a=subprocess.run(args or command(root),capture_output=True,text=True,timeout=30)
 assert (a.returncode==0)==ok,a.stdout+a.stderr
 return {'returncode':a.returncode,'stdout':a.stdout.strip(),'stderr':a.stderr.strip()}
before=run(R);C.mkdir()
for n in ['packet','work']:shutil.copytree(R/n,C/n)
for n in names:shutil.copy2(R/n,C/n)
baseline=run(C);tests=[]
def test(name,change,restore):
 try:change();tests.append({'name':name,'rejected':True,'result':run(C,False)})
 finally:restore()
p=C/'packet/public/review.md';pb=p.read_bytes()
test('changed_review',lambda:p.write_bytes(pb+b'\nmutation\n'),lambda:p.write_bytes(pb))
test('missing_review',lambda:p.unlink(),lambda:p.write_bytes(pb))
e=C/'packet/public/unlisted-control'
test('extra_payload',lambda:e.write_text('fixture only'),lambda:e.unlink())
s=C/'packet/public/link-control'
test('payload_symlink',lambda:s.symlink_to('review.md'),lambda:s.unlink())
for n in names:
 q=C/n;b=q.read_bytes()
 test('changed_'+n,lambda q=q,b=b:q.write_bytes(b+b' '),lambda q=q,b=b:q.write_bytes(b))
args=command(C);args[args.index('--manifest-sha256')+1]='0'*64
tests.append({'name':'wrong_external_anchor','rejected':True,'result':run(C,False,args)})
mp=C/'MANIFEST.json';mb=mp.read_bytes();fp=C/'FINAL.json';fb=fp.read_bytes()
def forge():
 p.write_bytes(pb+b'\nlocal reseal\n');m=json.loads(mb);e=next(x for x in m['entries'] if x['path']=='packet/public/review.md');e.update(size=p.stat().st_size,sha256=h(p));mp.write_text(json.dumps(m,indent=2)+'\n');f=json.loads(fb);f.update(manifest_sha256=h(mp),review_sha256=h(p));fp.write_text(json.dumps(f,indent=2)+'\n')
def restore():p.write_bytes(pb);mp.write_bytes(mb);fp.write_bytes(fb)
test('coherent_local_reseal_against_old_external_anchors',forge,restore)
aftercopy=run(C);after=run(R);assert before==after;assert all(h(R/n)==anchors[n] for n in names)
# Recheck original current r139/r140 byte/mode/link-count baseline after copied execution.
import stat
base=R.parents[3];now={}
for name in ['fresh-structural-discovery-r139','fresh-structural-discovery-r140']:
 root=R.parent/name
 for p in [root,*root.rglob('*')]:
  s=p.lstat();now[str(p.relative_to(base))]={'kind':'file' if p.is_file() else 'directory','mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink,**({'sha256':h(p),'size':s.st_size} if p.is_file() else {})}
assert now==json.loads((R/'packet/private/originals-before.json').read_text()),'original roots changed'
pres={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'r139_r140_exact_current_baseline_unchanged':True,'entries':len(now),'review_payload_verification_before_after_equal':True,'detached_seals_unchanged':True,'scope':'Artifact identities and current bytes/modes/link counts only; no historical whole-parent preservation, syscall-denial or mathematical gate'}
(R/'controls/preservation-after.json').write_text(json.dumps(pres,indent=2)+'\n')
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'ARTIFACT_CONTROLS_ONLY','external_baseline_anchors':anchors,'original_before':before,'copied_baseline':baseline,'negative_controls':tests,'restored_copy':aftercopy,'original_after':after,'original_r139_r140_preserved':True,'not_a_correctness_or_acceptance_gate':True}
(R/'controls/receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'negative_controls':len(tests),'receipt_sha256':h(R/'controls/receipt.json'),'preservation_sha256':h(R/'controls/preservation-after.json')}))
