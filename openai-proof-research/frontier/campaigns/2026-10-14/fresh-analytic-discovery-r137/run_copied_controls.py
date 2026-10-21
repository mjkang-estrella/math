"""Bounded artifact controls on three copied files, never on originals."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parent
C=R/'private/controls/copied-packet'
if C.exists():raise SystemExit('Controls already prepared; refusing overwrite')
C.mkdir(parents=True)
def sha(b):return hashlib.sha256(b).hexdigest()
sources={'derivation-copy.md':R/'DERIVATION.md','project-rules-copy.md':R/'private/originals/AGENTS.md','branching-copy.tex':next((R/'private/upstream/preprints').glob('Nonuniqueness-with-local-conservation*/build/paper/11-branching.tex'))}
before={k:sha(p.read_bytes()) for k,p in sources.items()}
for k,p in sources.items():(C/k).write_bytes(p.read_bytes())
(C/'FINAL.md').write_text('Copied integrity control only. No mathematical or research disposition.\n')
(C/'REPORT.md').write_text('Three copied local files; no full-source authentication test in this small control packet.\n')
excluded=['DETACHED-SHA256.json','FINAL.md','MANIFEST.json','REPORT.md']
m=dict(schema='r137-artifact-v1',excluded_envelopes=excluded,files=[dict(path=k,size=(C/k).stat().st_size,sha256=before[k]) for k in sorted(sources)])
(C/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
a={n:sha((C/n).read_bytes()) for n in ['MANIFEST.json','FINAL.md','REPORT.md']}
(C/'DETACHED-SHA256.json').write_text(json.dumps(a,indent=2)+'\n')
def run(name,expected,anchors=None):
 d=anchors or a
 cmd=[sys.executable,str(R/'verify_readonly.py'),'--root',str(C),'--manifest-sha256',d['MANIFEST.json'],'--final-sha256',d['FINAL.md'],'--report-sha256',d['REPORT.md']]
 x=subprocess.run(cmd,text=True,capture_output=True)
 if x.returncode!=expected:raise RuntimeError(name+': unexpected '+x.stdout+x.stderr)
 return dict(control=name,expected_exit=expected,observed_exit=x.returncode,stdout=x.stdout.strip(),stderr=x.stderr.strip())
results=[run('unchanged copied packet',0)]
p=C/'derivation-copy.md';b=p.read_bytes();p.write_bytes(b+b'\ncontrol mutation\n');results.append(run('payload byte mutation',1));p.write_bytes(b)
p=C/'extra.txt';p.write_text('control extra');results.append(run('extra payload member',1));p.unlink()
d=dict(a);d['FINAL.md']='0'*64;results.append(run('wrong detached caller anchor',1,d))
p=C/'project-rules-copy.md';b=p.read_bytes();p.unlink();results.append(run('missing payload member',1));p.write_bytes(b)
p=C/'link-control';p.symlink_to('branching-copy.tex');results.append(run('symlink member',1));p.unlink()
results.append(run('restored copied packet',0))
after={k:sha(p.read_bytes()) for k,p in sources.items()}
assert before==after
(R/'artifact-controls.json').write_text(json.dumps(dict(scope='Read-only byte-verifier controls on three copied files. Not mathematical gates or a full-packet/OS/history certificate.',source_before=before,source_after=after,copied_packet=str(C.relative_to(R)),anchors=a,results=results),indent=2)+'\n')
print('Copied artifact controls:',len(results),'expected outcomes; original sampled bytes unchanged across controls')
