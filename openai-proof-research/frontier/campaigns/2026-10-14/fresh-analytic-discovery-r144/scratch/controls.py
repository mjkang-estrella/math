from pathlib import Path
import hashlib, json, subprocess, sys, os
r=Path(__file__).resolve().parents[1]
assert not any((r/n).exists() for n in ['FINAL.md','MANIFEST.json','REPORT.md'])
f=r/'private/control-fixture';f.mkdir()
payload=(r/'GAPS.md').read_bytes()
(f/'selected-note.md').write_bytes(payload)
sha=lambda b:hashlib.sha256(b).hexdigest()
(f/'FINAL.md').write_text('Selected original prose fixture only.\n')
(f/'REPORT.md').write_text('Not an original research packet or mathematical gate.\n')
(f/'MANIFEST.json').write_text(json.dumps({'schema':'r144-exact-payload-v1','files':[
    {'path':'selected-note.md','size':len(payload),'sha256':sha(payload)}]},indent=2)+'\n')
anchors={n:sha((f/n).read_bytes()) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snapshot():
    return {p.relative_to(f).as_posix():sha(p.read_bytes()) for p in f.rglob('*') if p.is_file()}
def run(label,want,override=None):
    before=snapshot();an=override or anchors
    q=subprocess.run([sys.executable,'-B',str(r/'verify.py'),str(f),
        '--final',an['FINAL.md'],'--manifest',an['MANIFEST.json'],
        '--report',an['REPORT.md']],capture_output=True,text=True)
    assert (q.returncode==0)==want and before==snapshot(),(label,q.stdout,q.stderr)
    return {'case':label,'expected_accept':want,'returncode':q.returncode,
            'verifier_preserved_fixture_bytes':True}
out=[run('baseline',True)]
(f/'selected-note.md').write_bytes(payload+b'\nchanged\n')
out.append(run('changed payload',False));(f/'selected-note.md').write_bytes(payload)
(f/'.hidden-extra').write_text('unexpected\n')
out.append(run('hidden extra',False));(f/'.hidden-extra').unlink()
(f/'selected-note.md').unlink()
out.append(run('missing payload',False));(f/'selected-note.md').write_bytes(payload)
out.append(run('wrong detached manifest',False,{**anchors,'MANIFEST.json':'0'*64}))
out.append(run('restored',True))
(r/'CONTROL-RESULTS.json').write_text(json.dumps({'selected_original':'GAPS.md',
 'selected_original_sha256':sha(payload),'fixture_envelope_anchors':anchors,
 'controls':out,'scope':'Byte/membership checks only. Not mathematical gates.'},indent=2)+'\n')
print(json.dumps(out))
