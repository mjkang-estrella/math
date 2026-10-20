#!/usr/bin/env python3
"""Authenticate a contribution review and copied controls, without a correctness verdict."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

FINAL = '48b36b2809719eec8dbbaf8edd5afe34e96e3f6a3ca675580e7bb9fa04714485'
MANIFEST = '18f91f008f36a0b58893c9fecce1e2ec3d6702ca3e8df415f92638b8c3bdef0c'
REPORT = '2fba1d895b72b4fc0af1dc64bc3de08d5e972a7757ed1d029d457fe1611dc763'
REVIEW = 'bc2962e70cb1ebde10d62446bd5cf06b97cd3a75bd612a81b8d76f3e31c34bb7'
LIMITS = '36171a5c24bd198ad466fbd1158dfc24d600528a58e9aee75f9c135027236fbb'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def snapshot(root):
    out = {}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat(); v=[s.st_mode,s.st_nlink]
        if stat.S_ISREG(s.st_mode):
            v += [s.st_size,sha(p)]
        elif stat.S_ISLNK(s.st_mode):
            v += [os.readlink(p)]
        out[p.relative_to(root).as_posix()] = v
    return out

def run(args):
    r=subprocess.run([sys.executable,'-B',*map(str,args)],capture_output=True,text=True,
                     env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    return {'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}

def verify(root,project,anchor=FINAL):
    return run([root/'packet/public/verify.py','--root',root,'--project',project,
                '--final',anchor,'--manifest',MANIFEST,'--report',REPORT])

def main():
    parent=Path(__file__).resolve().parent
    campaign=parent.parents[1]
    review=campaign/'t184i134-contribution-r1'
    project=review.parents[3]
    anchors={'FINAL.json':FINAL,'packet/MANIFEST.json':MANIFEST,'REPORT.md':REPORT,
             'packet/public/review.md':REVIEW,'packet/public/reading-limits.md':LIMITS,
             'artifact-controls.json':'8dae6684bc5f5847b5bec301e34fdc04e4de392db0b4ec1e2e0966f1b21ee2f3',
             'unchanged.json':'fc425ca56285d190ec3bb804db9b1487ab50fb84749129d175d55251c22a1c76'}
    for rel,h in anchors.items():
        assert sha(review/rel)==h,rel
    inputs=json.loads((review/'packet/public/inputs.json').read_text())
    author=project/inputs['author_anchors']['root']
    before_review=snapshot(review); before_author=snapshot(author)
    contexts={rel:sha(project/rel) for rel in inputs['project_files']}
    assert contexts==inputs['project_files']
    # Supplement author verifier's Git-blob check with the exact canonical tree and receipt metadata.
    treepath=project/'sources/preprints-tree.json'; assert sha(treepath)==TREE
    td=json.loads(treepath.read_text()); assert td['truncated'] is False and len(td['tree'])==13223
    tree={r['path']:r for r in td['tree']}
    source=json.loads((review/'packet/private/source/receipts.json').read_text())
    assert source['pin']==PIN
    canonical=[]
    for r in source['files']:
        data=(review/'packet/private/source'/r['path']).read_bytes(); e=tree[r['path']]
        assert r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path']
        assert r['size']==len(data)==e['size'] and hashlib.sha256(data).hexdigest()==r['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==r['git_blob_sha1']==e['sha']
        canonical.append({'path':r['path'],'canonical_source_authenticated':True})
    direct=verify(review,project)
    with tempfile.TemporaryDirectory(prefix='copied-review-',dir=parent) as temp:
        copy=Path(temp)/'review'; shutil.copytree(review,copy,symlinks=True)
        copied=verify(copy,project); snap=snapshot(copy)
        wrong=verify(copy,project,'0'*64); wrong_unchanged=snap==snapshot(copy)
        receipt_path=Path(temp)/'controls.json'
        controls=run([copy/'packet/public/controls.py',copy,project,FINAL,MANIFEST,REPORT,receipt_path])
        receipt=json.loads(receipt_path.read_text())
    review_unchanged=before_review==snapshot(review); author_unchanged=before_author==snapshot(author)
    contexts_unchanged=contexts=={rel:sha(project/rel) for rel in contexts}
    ok=(direct['exit']==0 and copied['exit']==0 and wrong['exit']!=0 and wrong_unchanged
        and controls['exit']==0 and receipt['all_as_expected'] and receipt['original_packet_unchanged']
        and review_unchanged and author_unchanged and contexts_unchanged)
    out={'kind':'PARENT_CONTRIBUTION_ARTIFACT_ADOPTION','mathematical_gate':False,
         'detached_anchors':anchors,'original_verify':direct,'copy_verify':copied,
         'wrong_final':wrong,'wrong_final_copy_unchanged':wrong_unchanged,
         'copied_controls':controls,'copied_controls_receipt':receipt,
         'canonical_source_authentication':canonical,'stable_project_inputs':contexts,
         'whole_review_root_unchanged':review_unchanged,'whole_author_root_unchanged':author_unchanged,
         'stable_project_inputs_unchanged':contexts_unchanged,'all_expected':ok,
         'coverage_limits':'Review verifier checks sealed file bytes and file sets, not exact directory modes, hardlinks or syscall denial. Parent whole-root preservation snapshots include modes and link counts. Stray sealed pyc preserved locally, never executed/imported. No portable release.'}
    (parent/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'all_expected':ok,'copied_cases':len(receipt['cases']),
                      'sources':len(canonical),'stable_inputs':len(contexts),
                      'author_unchanged':author_unchanged,'review_unchanged':review_unchanged}))
    return 0 if ok else 1

if __name__=='__main__':
    sys.exit(main())
