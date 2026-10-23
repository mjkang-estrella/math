#!/usr/bin/env python3
"""Authenticate the contribution review without changing either original root."""
import datetime, hashlib, json, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
P=Path(__file__).resolve().parent; C=P.parent.parent; PROJECT=C.parents[2]
R=C/'structural-r195-contribution-r1'; A=C/'fresh-structural-discovery-r195'
ANCHORS={'FINAL.md':'faabeaa9dc4b502860f743877512baf661f8764e023732cdac349f0def430ace',
         'MANIFEST.json':'4d0874c0de7dbebc07b410d6cc8295a3748de856a2680894d80fd9572530f779',
         'REPORT.md':'858d830e1d9e54ab4d0c2950e9fb8ab64cd8b03e6cef9b1f4a5b707d8b5042a2'}
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snap(root):
    assert not any(p.is_symlink() for p in root.rglob('*'))
    return {str(p.relative_to(root)):(p.stat().st_size,sha(p),stat.S_IMODE(p.stat().st_mode)) for p in root.rglob('*') if p.is_file()}
def verify(root, anchors):
    return subprocess.run([sys.executable,'-I','-B',str(R/'verify_packet.py'),'--root',str(root),
                           '--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['MANIFEST.json'],
                           '--report-sha',anchors['REPORT.md']],capture_output=True,text=True,timeout=30)
def main():
    before=snap(R); abefore=snap(A)
    assert read(R/'ANCHORS.json')['sha256']==ANCHORS
    v=verify(R,ANCHORS);assert v.returncode==0,(v.stdout,v.stderr)
    m=read(R/'MANIFEST.json');assert len(m['files'])==67 and m['payload_bytes']==8105148
    selected=read(R/'private/selected-input-verification.json')
    for x in selected['baseline_files']:
        p=PROJECT/x['path'];assert (p.stat().st_size,sha(p),stat.S_IMODE(p.stat().st_mode))==(x['bytes'],x['sha256'],x['mode']),x['path']
    assert sum(not x['unchanged_from_entry_baseline'] for x in selected['baseline_files'])==1
    tree=read(PROJECT/'sources/preprints-tree.json');assert not tree['truncated'] and len(tree['tree'])==13223
    lookup={e['path']:e for e in tree['tree']};src=read(R/'private/source-authentication.json')['files'];assert len(src)==12
    for x in src:
        p=R/x['local'];b=p.read_bytes();e=lookup[x['path']]
        assert len(b)==x['bytes']==e['size'] and sha(p)==x['sha256']
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
        assert b==(A/x['local']).read_bytes()
    prefix=src[0]['path'].rsplit('/',1)[0]+'/'
    assert {x['path']for x in src}=={k for k,e in lookup.items()if k.startswith(prefix)and e['type']=='blob'}
    for x in selected['primary_originals']:
        p=PROJECT/x['path'];assert len(p.read_bytes())==x['bytes'] and sha(p)==x['sha256']
        assert stat.S_IMODE(p.stat().st_mode)==x['observed_original_mode'] and p.read_bytes()==(R/x['copy']).read_bytes()
    hist=read(R/'private/history-exact-selection.json');assert len(hist)==9
    for x in hist:
        start,end=x['extent']
        with (PROJECT/x['path']).open('rb')as f:f.seek(start);b=f.read(end-start)
        assert hashlib.sha256(b).hexdigest()==x['sha256'] and b==(R/x['copy']).read_bytes()
    fixture=R/'private/controls';ca=read(fixture/'ANCHORS.json')['sha256'];cases=[]
    with tempfile.TemporaryDirectory(prefix='s195-contribution-controls-',dir=P)as td:
        d=Path(td)/'fixture';shutil.copytree(fixture,d)
        def check(name, expected, aa=ca):
            r=verify(d,aa);assert (r.returncode==0)==expected,(name,r.stderr)
            cases.append({'case':name,'accepted':r.returncode==0})
        check('intact copied fixture',True)
        for name in ('PAYLOAD.md','FINAL.md','MANIFEST.json','REPORT.md'):
            p=d/name;b=p.read_bytes();p.write_bytes(b+b'!');check('changed '+name,False);p.write_bytes(b)
        p=d/'PAYLOAD.md';mode=stat.S_IMODE(p.stat().st_mode);p.chmod(mode^0o100);check('changed mode',False);p.chmod(mode)
        p=d/'extra.txt';p.write_text('extra');check('extra file',False);p.unlink()
        check('wrong REPORT anchor',False,{**ca,'REPORT.md':'0'*64});check('restored fixture',True)
    assert snap(R)==before and snap(A)==abefore
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,
            'anchors':ANCHORS,'verifier':json.loads(v.stdout),'source_blobs':12,'primary_originals':len(selected['primary_originals']),
            'history_extents':9,'baseline_inputs':len(selected['baseline_files']),'parent_assessment_drift_disclosed':True,
            'copied_controls':cases,'review_and_author_roots_unchanged':True,'review_sha256':sha(R/'REVIEW.md'),
            'frozen_scope_sha256':sha(A/'FROZEN.md'),'author_proof_sha256':sha(A/'AUTHOR-PROOF.md')}
    (P/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
