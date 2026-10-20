#!/usr/bin/env python3
"""Authenticate unchanged author artifacts; no mathematical/contribution judgment."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

FINAL = '27ee1a396bda9f1bf61a24177cf8a8e753033c5e73234c78071a74fa928bbdf9'
MANIFEST = '4264a6d43c8848418f01353f0cf3b8bb144b8dcc3943251712e8782cf6d967b0'
REPORT = '60c0a4806dd4135466d1b4cb553039ef01cac230db775424fc0bd9f72aab5b2f'
SCOPE = '4d491e34d80254c3b6b0d4d7a289500505bb2826fc4e4db4b3de55a92913221c'
PROOF = '0ec0b117efaeba1e692265d7f62810dedaf5010bc47f5b640bad066f63ea46e2'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def snapshot(root):
    out = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        v = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode):
            v += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode):
            v += [os.readlink(p)]
        out[p.relative_to(root).as_posix()] = v
    return out

def run(root, project, anchor=FINAL):
    args = [sys.executable, '-B', str(root/'packet/public/verify.py'),
            '--root', str(root), '--project', str(project)]
    if anchor is not None:
        args += ['--finalhash', anchor]
    p = subprocess.run(args, text=True, capture_output=True,
                       env={**os.environ, 'PYTHONDONTWRITEBYTECODE':'1'})
    return {'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr}

def main():
    parent = Path(__file__).resolve().parent
    author = parent.parent/'fresh-structural-discovery-r134'
    project = author.parents[3]
    anchors = {'FINAL.json':FINAL,'packet/MANIFEST.json':MANIFEST,'REPORT.md':REPORT,
               'packet/public/frozen-statement.md':SCOPE,'packet/public/proof.md':PROOF}
    for rel, h in anchors.items():
        assert sha(author/rel) == h, rel
    before = snapshot(author)
    external = []
    for line in (author/'scratch/inputs-before-seal.sha256').read_text().splitlines():
        h, rel = line.split('  ',1)
        external.append({'origin':rel,'expected':h,'actual':sha(project/rel)})
    direct = run(author, project)
    cases = []
    names = ['baseline','missing-detached-anchor','wrong-detached-anchor','tampered-proof',
             'tampered-frozen-statement','tampered-outside-report','extra-packet-file',
             'tampered-source-body','tampered-primary']
    source = next(iter(json.loads((author/'packet/private/source/receipts.json').read_text())))
    primary = next(iter(json.loads((author/'packet/private/primary/receipts.json').read_text())))
    with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=parent) as temp:
        for name in names:
            copy = Path(temp)/name
            shutil.copytree(author, copy, symlinks=True)
            rel = {'tampered-proof':'packet/public/proof.md',
                   'tampered-frozen-statement':'packet/public/frozen-statement.md',
                   'tampered-outside-report':'REPORT.md',
                   'tampered-source-body':'packet/private/source/'+source,
                   'tampered-primary':'packet/private/primary/'+primary}.get(name)
            if rel:
                with (copy/rel).open('ab') as f:
                    f.write(b'\nPARENT_CONTROL_MUTATION\n')
            if name == 'extra-packet-file':
                (copy/'packet/parent-extra').write_text('unexpected\n')
            copy_before = snapshot(copy)
            anchor = None if name=='missing-detached-anchor' else '0'*64 if name=='wrong-detached-anchor' else FINAL
            result = run(copy,project,anchor)
            unchanged = copy_before == snapshot(copy)
            expected = result['exit']==0 if name=='baseline' else result['exit']!=0
            cases.append({'case':name,'expected_result':expected,'copy_unchanged':unchanged,**result})
            shutil.rmtree(copy)
    # Reproduce the bounded author diagnostic; approximate stationary points are not a proof.
    diag = subprocess.run([sys.executable,'-B',str(author/'packet/public/sanity.py')],
                          text=True,capture_output=True,timeout=60,
                          env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    diagnostic = {'exit':diag.returncode,'stdout':diag.stdout,'stderr':diag.stderr,
                  'limit':'Approximate stationary points; not global-maximizer certificates or a mathematical gate.'}
    external_unchanged = all(sha(project/r['origin'])==r['actual'] for r in external)
    author_unchanged = before == snapshot(author)
    ok = (direct['exit']==0 and all(r['expected_result'] and r['copy_unchanged'] for r in cases)
          and all(r['expected']==r['actual'] for r in external) and external_unchanged
          and author_unchanged and diag.returncode==0)
    out = {'kind':'PARENT_AUTHOR_ARTIFACT_INTAKE_ONLY','mathematical_gate':False,
           'detached_anchors':anchors,'original_verify':direct,'copied_cases':cases,
           'diagnostic':diagnostic,'external_inputs_at_parent_intake':external,
           'external_inputs_unchanged_during_parent_replay':external_unchanged,
           'whole_author_root_unchanged':author_unchanged,'all_expected':ok,
           'coverage_limits':'Author verifier checks bytes and exact paths, not modes or hardlinks. Parent unchanged snapshots include modes/link counts. External-input hash list was recorded near author seal, not a full-round change audit; live campaign ledger can change after this intake.'}
    (parent/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'all_expected':ok,'cases':len(cases),'external_inputs':len(external),
                      'whole_author_root_unchanged':author_unchanged,'diagnostic':diagnostic}))
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())
