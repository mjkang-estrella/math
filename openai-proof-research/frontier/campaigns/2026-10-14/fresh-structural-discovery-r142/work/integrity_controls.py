from pathlib import Path
import hashlib,json,subprocess,sys,os
R=Path(__file__).resolve().parents[1]
C=R/'packet/private/copied-integrity-control';C.mkdir(exist_ok=True)
for src,name in [('verify_packet.py','verifier.py'),('interval_betti.py','payload.py')]:
 (C/name).write_bytes((R/'packet/public'/src).read_bytes())
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
(C/'outsideREPORT.md').write_text('Copied miniature integrity fixture. No mathematical gate.\n')
(C/'MANIFEST.json').write_text(json.dumps({'files':[dict(path=p.name,sha256=h(p),bytes=p.stat().st_size) for p in [C/'payload.py',C/'verifier.py']]},indent=2)+'\n')
(C/'FINAL.json').write_text(json.dumps(dict(manifest_sha256=h(C/'MANIFEST.json'),outside_report_sha256=h(C/'outsideREPORT.md')),indent=2)+'\n')
a={x:h(C/x) for x in ['MANIFEST.json','FINAL.json','outsideREPORT.md']}
(C/'ANCHORS.json').write_text(json.dumps(a,indent=2)+'\n')
cmd=[sys.executable,str(C/'verifier.py'),str(C),'--manifest-sha256',a['MANIFEST.json'],'--final-sha256',a['FINAL.json'],'--report-sha256',a['outsideREPORT.md']]
rows=[]
def run(label,expected,override=None):
 p=subprocess.run(override or cmd,capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
 ok=(p.returncode==0)
 if ok!=expected:raise AssertionError((label,p.stdout,p.stderr))
 rows.append(dict(control=label,accepted=ok,expected_acceptance=expected))
run('unaltered copied fixture',True)
p=C/'payload.py';b=p.read_bytes();p.write_bytes(b+b'\n# controlled mutation\n');run('payload mutation',False);p.write_bytes(b)
x=C/'extra.txt';x.write_text('extra');run('extra file',False);x.unlink()
p.unlink();run('missing payload',False);p.write_bytes(b)
bad=cmd.copy();bad[bad.index('--manifest-sha256')+1]='0'*64;run('wrong explicit detached anchor',False,bad)
run('restored copied fixture',True)
(R/'packet/private/integrity-controls.json').write_text(json.dumps(dict(scope='Copied miniature artifact controls only',controls=rows),indent=2)+'\n')
print(json.dumps(rows))
