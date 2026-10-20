#!/usr/bin/env python3
# Original code, MIT. Mutates only this root's controls/copy fixture.
import hashlib,json,shutil,subprocess,sys
from datetime import datetime,timezone
from pathlib import Path
R=Path(__file__).resolve().parents[1]
C=R/'controls'/'copy'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
names=['MANIFEST.json','outsideREPORT.md','FINAL.json']
anchors={n:sha(R/n) for n in names}
def cmd(root):
    return [sys.executable,'-B',str(root/'packet/public/verify.py'),'--root',str(root),
            '--manifest-sha256',anchors[names[0]],'--report-sha256',anchors[names[1]],
            '--final-sha256',anchors[names[2]]]
def run(root,ok=True,args=None):
    p=subprocess.run(args or cmd(root),capture_output=True,text=True,timeout=30)
    if (p.returncode==0)!=ok:raise RuntimeError('unexpected control result: '+p.stdout+p.stderr)
    return {'returncode':p.returncode,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()}
if C.exists():raise SystemExit('Refusing to overwrite existing copied fixture')
before=run(R)
C.mkdir(parents=True)
for top in ['packet','work']:shutil.copytree(R/top,C/top)
for n in names:shutil.copy2(R/n,C/n)
baseline=run(C)
tests=[]
def mutate(label,fn,undo):
    try:
        fn();result=run(C,False);tests.append(dict(name=label,rejected=True,result=result))
    finally:undo()
p=C/'packet/public/author-proof.md';original=p.read_bytes()
mutate('payload_bit_flip',lambda:p.write_bytes(original+b'\nchanged\n'),lambda:p.write_bytes(original))
mutate('payload_missing',lambda:p.unlink(),lambda:p.write_bytes(original))
e=C/'packet/public/unlisted-control.txt'
mutate('payload_extra',lambda:e.write_text('fixture only'),lambda:e.unlink())
for n in names:
    q=C/n;b=q.read_bytes()
    mutate('changed_'+n,lambda q=q,b=b:q.write_bytes(b+b' '),lambda q=q,b=b:q.write_bytes(b))
args=cmd(C);args[args.index('--manifest-sha256')+1]='0'*64
tests.append(dict(name='wrong_detached_anchor',rejected=True,result=run(C,False,args)))
s=C/'packet/public/symlink-control'
mutate('payload_symlink',lambda:s.symlink_to('author-proof.md'),lambda:s.unlink())
# A self-consistent local rewrite still cannot replace the externally held anchors.
mp=C/'MANIFEST.json';fp=C/'FINAL.json';mb=mp.read_bytes();fb=fp.read_bytes()
def reseal():
    p.write_bytes(original+b'\nlocal forgery\n')
    m=json.loads(mb)
    row=next(x for x in m['entries'] if x['path']=='packet/public/author-proof.md')
    row.update(size=p.stat().st_size,sha256=sha(p))
    mp.write_text(json.dumps(m,indent=2)+'\n')
    f=json.loads(fb);f['manifest_sha256']=sha(mp)
    fp.write_text(json.dumps(f,indent=2)+'\n')
def restore():
    p.write_bytes(original);mp.write_bytes(mb);fp.write_bytes(fb)
mutate('self_consistent_local_reseal_with_old_external_anchors',reseal,restore)
diagnostic=subprocess.run([sys.executable,'-B',str(C/'packet/public/finite_check.py')],capture_output=True,text=True,timeout=60)
if diagnostic.returncode:raise RuntimeError(diagnostic.stderr)
replayed=json.loads(diagnostic.stdout)
if replayed!=json.loads((C/'packet/private/finite-check.json').read_text()):raise RuntimeError('finite replay changed')
after_copy=run(C);after_original=run(R)
if before!=after_original:raise RuntimeError('original verification changed')
if any(sha(R/n)!=anchors[n] for n in names):raise RuntimeError('original anchor changed')
receipt=dict(observed_utc=datetime.now(timezone.utc).isoformat(),status='LOCAL_ARTIFACT_CONTROLS_ONLY',
             detached_original_anchors=anchors,original_before=before,copied_baseline=baseline,
             mutation_controls=tests,finite_diagnostic_replay_equal=True,
             copied_after_restore=after_copy,original_after=after_original,
             scope='Artifact integrity and bounded diagnostic replay; no independent mathematical, contribution, formal or release gate.')
out=R/'controls'/'receipt.json'
out.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'receipt':str(out.relative_to(R)),'sha256':sha(out),'negative_controls':len(tests),'finite_replay_equal':True}))
