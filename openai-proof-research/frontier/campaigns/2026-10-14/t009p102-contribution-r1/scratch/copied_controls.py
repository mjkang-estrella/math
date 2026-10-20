"""Small disposable preseal fixtures, exclusively in this review root."""
import hashlib, json, os, pathlib, runpy, shutil, subprocess, sys
sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[1]
ns = runpy.run_path(str(ROOT/'verify.py'))
digest, inventory = ns['digest'], ns['inventory']
work = ROOT/'scratch/fixture-work'
assert not work.exists()
before = inventory(ROOT)
work.mkdir()
seed = work/'seed'
(seed/'public').mkdir(parents=True)
(seed/'private').mkdir()
(seed/'public/REVIEW.md').write_text('Original copied integrity fixture; no mathematics.\n')
shutil.copy2(ROOT/'public/SCOPE.md', seed/'public/SCOPE.md')
(seed/'private/evidence.bin').write_bytes(b'Protected-evidence fixture, not a source body.\n')

def seal_fixture(root):
    (root/'REPORT.md').write_text('Outside copied preseal fixture report.\n')
    (root/'MANIFEST.json').write_text(json.dumps(inventory(root),sort_keys=True,indent=2)+'\n')
    final = {'manifest_sha256':digest(root/'MANIFEST.json'), 'report_sha256':digest(root/'REPORT.md'), 'scope_sha256':ns['SCOPE'], 'review_sha256':digest(root/'public/REVIEW.md'), 'contribution':'TECHNICAL_CONDITIONAL_ON_CORRECTNESS', 'correctness_gate':'NOT_PERFORMED'}
    (root/'FINAL.json').write_text(json.dumps(final,sort_keys=True,indent=2)+'\n')
    return {key:digest(root/name) for key,name in [('final','FINAL.json'),('manifest','MANIFEST.json'),('report','REPORT.md')]}

anchors = seal_fixture(seed)
results = []
for case in ['clean','prose-byte','missing-evidence','unexpected-hidden','symlink','mode','outside-report','wrong-final','forged-reseal']:
    q = work/'copy'
    shutil.copytree(seed,q)
    a = dict(anchors)
    if case == 'prose-byte': (q/'public/REVIEW.md').write_text('changed\n')
    elif case == 'missing-evidence': (q/'private/evidence.bin').unlink()
    elif case == 'unexpected-hidden': (q/'.unexpected').write_text('extra\n')
    elif case == 'symlink':
        p=q/'public/REVIEW.md';p.unlink();p.symlink_to(seed/'public/REVIEW.md')
    elif case == 'mode': (q/'public/REVIEW.md').chmod(0o600)
    elif case == 'outside-report': (q/'REPORT.md').write_text('changed report\n')
    elif case == 'wrong-final': a['final']='0'*64
    elif case == 'forged-reseal':
        (q/'public/REVIEW.md').write_text('forged review\n');seal_fixture(q)
    cmd=[sys.executable,'-B',str(ROOT/'verify.py'),'--root',str(q)]
    for key,val in a.items():cmd += ['--'+key+'-sha256',val]
    p=subprocess.run(cmd,capture_output=True,text=True)
    results.append({'case':case,'expected_accept':case=='clean','actual_accept':p.returncode==0,'returncode':p.returncode,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()})
    shutil.rmtree(q)
shutil.rmtree(work)
assert inventory(ROOT) == before, 'existing review payload changed during controls'
assert all(x['expected_accept']==x['actual_accept'] for x in results)
(ROOT/'controls').mkdir(exist_ok=True)
(ROOT/'controls/results.json').write_text(json.dumps({'artifact_only':True,'fixture_anchors':anchors,'cases':results,'existing_review_tree_unchanged_during_controls':True,'limits':'Nine small fresh preseal copies. No source or author writer executed; no mathematical tests. Fixtures removed before production seal.'},indent=2)+'\n')
print('Nine copied artifact cases behaved as expected; original fixture tree removed.')
