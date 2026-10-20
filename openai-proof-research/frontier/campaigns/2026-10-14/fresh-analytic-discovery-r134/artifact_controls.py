#!/usr/bin/env python3
"""Bounded controls on one disposable copy; source packet is never mutated."""
from pathlib import Path
import datetime, hashlib, json, shutil, subprocess, sys, tempfile
R=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
anchors={n:sha(R/n) for n in ['MANIFEST.json','FINAL.json','REPORT.md','verify.py']}
def vector():
    return {x.relative_to(R).as_posix():sha(x) for x in sorted((R/'packet').rglob('*')) if x.is_file()} | anchors
before=vector()
args=['--manifest-sha256',anchors['MANIFEST.json'],'--final-sha256',anchors['FINAL.json'],'--report-sha256',anchors['REPORT.md']]
def run(root):
    p=subprocess.run([sys.executable,'-B',str(root/'verify.py'),'--root',str(root),*args],capture_output=True,text=True,timeout=30)
    return {'returncode':p.returncode,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()}
checks=[]
def test(name,root,should_pass):
    x=run(root);ok=(x['returncode']==0)==should_pass
    checks.append({'name':name,'expected_pass':should_pass,'control_pass':ok,**x})
    if not ok:raise AssertionError(name)
work=R/'work';work.mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='copied-integrity-',dir=work) as tmp:
    C=Path(tmp)
    shutil.copytree(R/'packet',C/'packet')
    for n in anchors:shutil.copy2(R/n,C/n)
    test('original_read_only_baseline',R,True)
    test('copied_baseline',C,True)
    p=C/'packet/public/author-proof.md';b=p.read_bytes();p.write_bytes(b+b'\nmutation\n')
    test('payload_mutation',C,False);p.write_bytes(b)
    p=C/'packet/unmanifested.txt';p.write_text('mutation')
    test('unexpected_payload_file',C,False);p.unlink()
    p=C/'REPORT.md';b=p.read_bytes();p.write_bytes(b+b'\nmutation\n')
    test('outside_report_mutation',C,False);p.write_bytes(b)
    p=C/'packet/public/FROZEN-SCOPE.md';b=p.read_bytes();p.unlink();p.symlink_to('author-proof.md')
    test('payload_symlink',C,False);p.unlink();p.write_bytes(b)
    p=C/'verify.py';b=p.read_bytes();p.write_bytes(b+b'\n# mutation\n')
    test('verifier_identity_mutation',C,False);p.write_bytes(b)
    # A locally recomputed manifest and FINAL cannot replace detached handoff anchors.
    p=C/'packet/public/author-proof.md';b=p.read_bytes();p.write_bytes(b+b'\nforged reseal\n')
    m=json.loads((C/'MANIFEST.json').read_text())
    for row in m['files']:
        q=C/row['path'];row.update(bytes=q.stat().st_size,sha256=sha(q))
    (C/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
    f=json.loads((C/'FINAL.json').read_text());f['manifest_sha256']=sha(C/'MANIFEST.json')
    (C/'FINAL.json').write_text(json.dumps(f,indent=2)+'\n')
    test('forged_local_reseal_against_original_detached_anchors',C,False)
    test('original_after_copied_mutations',R,True)
after=vector()
assert before==after
receipt={'status':'PASS_ARTIFACT_CONTROLS_ONLY','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'originals_unchanged':before==after,'copy_removed':True,'checks':checks,'anchors_used':anchors,'limits':'No mathematical gate. No original payload mutation. One disposable copy inside the exclusive root; removed after controls.'}
(R/'INTEGRITY-CONTROLS.json').write_text(json.dumps(receipt,indent=2)+'\n')
# Compare exact late-bound originals; parent ledger is explicitly mutable.
rows=[]
for x in json.loads((R/'packet/private/late-bindings.json').read_text()):
    p=Path(x['original_path']);now=sha(p) if p.is_file() else None
    rows.append({'path':x['original_path'],'captured_sha256':x['sha256'],'handoff_sha256':now,'same_bytes':now==x['sha256'],'mutable_observation':x['mutable_observation']})
source=[]
for x in json.loads((R/'packet/private/source-acquisition.json').read_text()):
    p=R/'packet/private/source'/Path(x['local']).name
    b=p.read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    source.append({'path':x['path'],'same_bytes':sha(p)==x['sha256'],'gitblob_matches':blob==x['sha'],'size_matches':len(b)==x['size']})
assert all(x['same_bytes'] and x['gitblob_matches'] and x['size_matches'] for x in source)
assert all(x['same_bytes'] for x in rows if not x['mutable_observation'])
(R/'ORIGINAL-PRESERVATION.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Exact late-captured inputs and acquired pinned source copies only; no historical whole-parent assertion. R041 was read once and was not rebound.','late_input_comparisons':rows,'pinned_source_comparisons':source,'immutable_payload_unchanged_by_controls':before==after},indent=2)+'\n')
print(json.dumps({'artifact_controls':len(checks),'all_expected_outcomes':True,'packet_unchanged':True,'late_original_bindings':len(rows),'late_mutable_changed':[x['path'] for x in rows if not x['same_bytes']],'source_blobs_rechecked':len(source)},indent=2))
