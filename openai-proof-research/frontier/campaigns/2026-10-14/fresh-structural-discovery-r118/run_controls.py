"""Original MIT code. Integrity controls on copies only; no mathematical gates."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile
root=Path(__file__).resolve().parent; packet=root/'packet'; work=root/'controls'; work.mkdir(exist_ok=True)
anchors=json.loads((root/'FINAL-ANCHORS.json').read_text()); tree=root.parents[3]/'sources/preprints-tree.json'
verifier=packet/'public/verify.py'
def sha(b): return hashlib.sha256(b).hexdigest()
def snapshot():
    return [(p.relative_to(packet).as_posix(),p.lstat().st_mode,p.lstat().st_nlink,sha(p.read_bytes()) if p.is_file() else None) for p in sorted(packet.rglob('*'))]
before=snapshot(); results=[]
cases=['valid','missing-finalhash','missing-reporthash','wrong-finalhash','wrong-reporthash','malformed-finalhash','modified-report','deleted-file','extra-file','extra-directory','symlink-file','symlink-directory','hardlink-file','mode-change','modified-manifest','coherent-reseal-old-anchor','modified-upstream','modified-primary','modified-verifier','wrong-tree']
for case in cases:
    with tempfile.TemporaryDirectory(prefix='r118-',dir=work) as temp:
        d=Path(temp); cp=d/'packet'; shutil.copytree(packet,cp)
        final=anchors['finalhash']; report=anchors['reporthash']; tp=tree
        if case=='wrong-finalhash': final='0'*64
        if case=='wrong-reporthash': report='0'*64
        if case=='malformed-finalhash': final='BAD'
        if case=='modified-report': (cp/'public/report.md').write_text('changed')
        if case=='deleted-file': (cp/'public/screens.md').unlink()
        if case=='extra-file': (cp/'public/extra.txt').write_text('extra')
        if case=='extra-directory': (cp/'public/extra').mkdir()
        if case=='symlink-file':
            (cp/'public/screens.md').unlink(); (cp/'public/screens.md').symlink_to('report.md')
        if case=='symlink-directory': (cp/'extra').symlink_to(cp/'public',target_is_directory=True)
        if case=='hardlink-file':
            (cp/'public/screens.md').unlink(); os.link(cp/'public/report.md',cp/'public/screens.md')
        if case=='mode-change': (cp/'public/screens.md').chmod(0o600)
        if case=='modified-manifest':
            with (cp/'MANIFEST.json').open('ab') as f: f.write(b' ')
        if case=='coherent-reseal-old-anchor':
            (cp/'public/report.md').write_text('coherent replacement report\n')
            m=json.loads((cp/'MANIFEST.json').read_text()); new=sha((cp/'public/report.md').read_bytes())
            m['report']['sha256']=new
            for row in m['files']:
                if row['path']=='public/report.md': row['sha256']=new; row['bytes']=(cp/'public/report.md').stat().st_size
            (cp/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
        if case=='modified-upstream':
            target=next((cp/'private/upstream').rglob('*.tex'))
            with target.open('ab') as f:f.write(b'\nchanged')
        if case=='modified-primary':
            target=cp/'private/primary/boolean-v3.pdf'
            with target.open('ab') as f:f.write(b'changed')
        if case=='modified-verifier':
            with (cp/'public/verify.py').open('ab') as f:f.write(b'\n# changed')
        if case=='wrong-tree': tp=d/'tree.json'; tp.write_text('{"truncated":true,"tree":[]}')
        cmd=[sys.executable,'-B',str(verifier),'--packet',str(cp),'--tree',str(tp)]
        if case!='missing-finalhash': cmd+=['--finalhash',final]
        if case!='missing-reporthash': cmd+=['--reporthash',report]
        r=subprocess.run(cmd,capture_output=True,text=True,timeout=20)
        expected=case=='valid'; ok=(r.returncode==0)==expected
        results.append({'case':case,'expected_accept':expected,'returncode':r.returncode,'matched_expectation':ok,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        if not ok: raise RuntimeError('unexpected control '+case)
after=snapshot(); assert before==after,'ORIGINAL CHANGED'
cmd=[sys.executable,'-B',str(verifier),'--packet',str(packet),'--finalhash',anchors['finalhash'],'--reporthash',anchors['reporthash'],'--tree',str(tree)]
r=subprocess.run(cmd,capture_output=True,text=True,timeout=20); assert r.returncode==0,r.stderr
(root/'VERIFICATION.json').write_text(json.dumps({'command':cmd,'returncode':r.returncode,'result':json.loads(r.stdout),'original_inventory_unchanged':True},indent=2)+'\n')
out={'control_count':len(results),'all_expectations_met':True,'original_inventory_unchanged':True,'original_snapshot_sha256':sha(json.dumps(before).encode()),'finalhash':anchors['finalhash'],'reporthash':anchors['reporthash'],'mathematical_gate':False,'results':results}
(work/'results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='results'},indent=2))
