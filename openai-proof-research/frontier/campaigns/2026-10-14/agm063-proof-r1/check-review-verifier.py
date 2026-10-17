#!/usr/bin/env python3
"""Independent controls on an isolated copy; writes only in this owned directory."""
import hashlib,json,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def snapshot(root):
    return {p.relative_to(root).as_posix(): ('dir' if p.is_dir() else hashlib.sha256(p.read_bytes()).hexdigest()) for p in root.rglob('*')}

def manifest(root):
    rows=[]; dirs=[]
    for p in sorted(root.rglob('*')):
        name=p.relative_to(root).as_posix()
        if p.is_dir(): dirs.append(name)
        elif name!='review-manifest.json':
            b=p.read_bytes(); rows.append({'path':name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    data={'schema':'AGM063-independent-proof-review-r1','verdict':'PASS_FULL_AGM063','full_formalization':False,'acceptance_claimed':False,'files':rows,'directories':dirs}
    raw=(json.dumps(data,indent=2)+'\n').encode(); (root/'review-manifest.json').write_bytes(raw)
    return hashlib.sha256(raw).hexdigest()

records=[]
with tempfile.TemporaryDirectory(prefix='verifier-controls-',dir=ROOT) as td:
    copy=Path(td)/'packet'; copy.mkdir()
    for p in ROOT.iterdir():
        if p==Path(td) or p.name=='review-manifest.json': continue
        if p.is_dir(): shutil.copytree(p,copy/p.name)
        else: shutil.copyfile(p,copy/p.name)
    anchor=manifest(copy)
    def run(name,expected,used_anchor=anchor):
        before=snapshot(copy)
        proc=subprocess.run(['python','-B',str(ROOT/'verify.py'),'--root',str(copy),'--anchor',used_anchor],capture_output=True,text=True)
        unchanged=snapshot(copy)==before
        records.append({'name':name,'returncode':proc.returncode,'stdout':proc.stdout,'stderr':proc.stderr,'expected_pass':expected,'no_writes':unchanged})
        assert (proc.returncode==0)==expected and unchanged,name
    run('positive-copy',True)
    run('wrong-anchor',False,'0'*64)
    p=copy/'review.md'; original=p.read_bytes(); p.write_bytes(original+b'\nTAMPER\n'); run('changed-review',False); p.write_bytes(original)
    p=copy/'reading-limits.md'; original=p.read_bytes(); p.unlink(); run('missing-reading-limits',False); p.write_bytes(original)
    p=copy/'extra'; p.write_text('extra'); run('extra-file',False); p.unlink()
    p=copy/'extra-dir'; p.mkdir(); run('extra-directory',False); p.rmdir()
    p=copy/'link'; p.symlink_to('review.md'); run('symlink',False); p.unlink()
    p=copy/'review-manifest.json'; original=p.read_bytes(); p.write_bytes(original+b' '); run('changed-manifest',False); p.write_bytes(original)
    raw=original.decode().replace('{','{"schema":"duplicate",',1); p.write_text(raw)
    run('duplicate-key-even-with-matching-anchor',False,hashlib.sha256(raw.encode()).hexdigest()); p.write_bytes(original)
    run('restored-positive',True)
(ROOT/'evidence/review-verifier-controls.json').write_text(json.dumps({'method':'Actual verifier subprocesses on isolated copies; every invocation checked for zero writes.','records':records,'all_expected':True},indent=2)+'\n')
print(json.dumps({'controls':len(records),'all_expected':True,'all_read_only':True}))
