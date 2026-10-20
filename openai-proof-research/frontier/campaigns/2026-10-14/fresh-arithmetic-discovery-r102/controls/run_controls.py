#!/usr/bin/env python3
"""Exercise only copied fixtures inside r102; never alter the research originals."""
import hashlib,json,os,runpy,shutil,stat,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[1]
PROJECT=R.parents[3]
ns=runpy.run_path(str(R/'verify.py'))
inv=ns['inventory'];digest=ns['digest']
TMP=R/'scratch'/'control-work'
assert not TMP.exists()
# Snapshot named originals, not an entire-workspace claim.
originals={}
for name in ['context','history']:
    for x in json.loads((R/f'private/{name}/bindings.json').read_text()):
        p=PROJECT/x['original'];originals[str(p)]=digest(p)
before=inv(R)
TMP.mkdir()
seed=TMP/'seed';seed.mkdir()
for p in R.iterdir():
    if p.name in ns['OUTSIDE']:continue
    if p.name=='scratch':
        (seed/'scratch').mkdir()
        for q in p.iterdir():
            if q==TMP:continue
            if q.is_dir():shutil.copytree(q,seed/'scratch'/q.name)
            else:shutil.copy2(q,seed/'scratch'/q.name)
    elif p.is_dir():shutil.copytree(p,seed/p.name)
    else:shutil.copy2(p,seed/p.name)
def seal_fixture(root):
    (root/'REPORT.md').write_text('Copied preseal integrity fixture only; no mathematical verdict.\n')
    (root/'MANIFEST.json').write_text(json.dumps(inv(root),sort_keys=True,indent=2)+'\n')
    (root/'FINAL.json').write_text(json.dumps({'manifest_sha256':digest(root/'MANIFEST.json'),'report_sha256':digest(root/'REPORT.md'),'scope_sha256':ns['SCOPE'],'proof_sha256':digest(root/'public/PROOF.md'),'mathematical_gates':'UNREVIEWED'},sort_keys=True,indent=2)+'\n')
    return {n:digest(root/f) for n,f in [('final','FINAL.json'),('manifest','MANIFEST.json'),('report','REPORT.md')]}
anchors=seal_fixture(seed)
cases=['clean','payload-byte','missing-body','unexpected-hidden','symlink','mode','outside-report','wrong-final-anchor','forged-reseal']
results=[]
for case in cases:
    q=TMP/'copy';shutil.copytree(seed,q)
    a=dict(anchors)
    if case=='payload-byte':
        with (q/'public/PROOF.md').open('ab') as f:f.write(b'\nMUTATION\n')
    elif case=='missing-body':
        x=json.loads((q/'private/acquisitions/register.json').read_text())[0];(q/x['local']).unlink()
    elif case=='unexpected-hidden':(q/'.unexpected').write_text('extra')
    elif case=='symlink':
        p=q/'public/PROOF.md';p.unlink();p.symlink_to(R/'public/PROOF.md')
    elif case=='mode':(q/'public/PROOF.md').chmod(0o600)
    elif case=='outside-report':(q/'REPORT.md').write_text('mutated outside report\n')
    elif case=='wrong-final-anchor':a['final']='0'*64
    elif case=='forged-reseal':
        with (q/'public/PROOF.md').open('ab') as f:f.write(b'\nFORGED\n')
        seal_fixture(q) # Keep the original external anchors.
    cmd=[sys.executable,'-B',str(R/'verify.py'),'--root',str(q)]
    for k,v in a.items():cmd+=['--'+k+'-sha256',v]
    out=subprocess.run(cmd,capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    expected=(case=='clean');observed=(out.returncode==0)
    results.append({'case':case,'expected_accept':expected,'actual_accept':observed,'returncode':out.returncode,'stdout':out.stdout.strip(),'stderr':out.stderr.strip()})
    shutil.rmtree(q)
shutil.rmtree(TMP)
after=inv(R)
assert before==after,'research root changed during copied controls'
assert all(digest(Path(p))==h for p,h in originals.items()),'named original changed during controls'
assert all(x['expected_accept']==x['actual_accept'] for x in results),'unexpected control result'
receipt={'artifact_controls_only':True,'fixture_anchors':anchors,'cases':results,'owned_existing_tree_unchanged_during_controls':True,'named_originals_unchanged_during_controls':len(originals),'limits':'Fresh preseal copies, not mathematical tests. Only named external originals and existing r102 tree compared. Fixture trees removed; original research payload never resealed or mutated.','verifier_sha256':digest(R/'verify.py')}
(R/'controls/results.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'copied_cases':len(results),'expected_outcomes':True,'named_originals_unchanged':len(originals),'mathematical_gate':False}))
