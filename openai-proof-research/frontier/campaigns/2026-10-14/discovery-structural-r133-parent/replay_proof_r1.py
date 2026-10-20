#!/usr/bin/env python3
"""Parent intake of independent correctness review r1; artifact checks are not proof review."""
import hashlib, json, os, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
FINAL='b7bbc75e13ad24dd4ce9aeea11911d16ec61817dbf3c240f09bb134f14313752'
MANIFEST='9939e7ab60fd1a004d9f20c7ec74a75a86473d5f83573ad175fed311e02b65ca'
REPORT='e701e9ac13ca2be3d9a024069d34b03ad746555162c089a17aabfe45f90c3363'
REVIEW='991e748640f3003ff044e9f3f395558b52b14bb3864f202f3dd58843139e22bb'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat(); rec=[s.st_mode,s.st_nlink]
        if stat.S_ISREG(s.st_mode): rec += [s.st_size,sha(p)]
        elif stat.S_ISLNK(s.st_mode): rec += [os.readlink(p)]
        out[p.relative_to(root).as_posix()]=rec
    return out
def run(args,cwd):
    r=subprocess.run([sys.executable,'-B',*args],cwd=cwd,capture_output=True,text=True,
                     env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    return {'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
def main():
    parent=Path(__file__).resolve().parent; campaign=parent.parent; repo=campaign.parents[2]
    review=campaign/'t106o133-proof-r1'
    assert sha(review/'FINAL.json')==FINAL and sha(review/'packet/MANIFEST.json')==MANIFEST
    assert sha(review/'REPORT.md')==REPORT and sha(review/'packet/public/review.md')==REVIEW
    fp=json.loads((review/'packet/public/input-fingerprints.json').read_text())
    author=repo/fp['author_root']
    before={'author':snapshot(author),'review':snapshot(review),
            'context':{n:sha(repo/n) for n in fp['context_files']}}
    common=['--root','.', '--project',str(repo),'--finalhash',FINAL]
    original=run(['packet/public/verify.py',*common],review)
    with tempfile.TemporaryDirectory(prefix='proof-r1-copy-',dir=parent) as td:
        copy=Path(td)/'review';shutil.copytree(review,copy,symlinks=True)
        verified=run(['packet/public/verify.py',*common],copy)
        bad=list(common);bad[-1]='0'*64
        wrong=run(['packet/public/verify.py',*bad],copy)
        controls=run(['packet/public/controls.py',*common],copy)
        receipt=json.loads((copy/'controls/artifact-controls.json').read_text())
    after={'author':snapshot(author),'review':snapshot(review),
           'context':{n:sha(repo/n) for n in fp['context_files']}}
    ok=(original['exit']==0 and verified['exit']==0 and wrong['exit']!=0
        and controls['exit']==0 and receipt['all_ok'] and before==after)
    out={'kind':'PARENT_REVIEW_ARTIFACT_INTAKE','mathematical_gate':False,
         'detached_anchors':{'final':FINAL,'manifest':MANIFEST,'report':REPORT,'review':REVIEW},
         'original_verify':original,'copied_verify':verified,'wrong_final':wrong,
         'copied_controls':controls,'control_receipt':receipt,
         'actual_author_unchanged':before['author']==after['author'],
         'actual_review_unchanged':before['review']==after['review'],
         'actual_context_unchanged':before['context']==after['context'],
         'author_file_count':len(fp['author_files']),'context_count':len(fp['context_files']),
         'all_expected':ok}
    (parent/'proof-r1-replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ['all_expected','actual_author_unchanged','actual_review_unchanged',
                                       'actual_context_unchanged','author_file_count','context_count']}))
    print('Copied controls:',len(receipt['controls']))
    return 0 if ok else 1
if __name__=='__main__':sys.exit(main())
