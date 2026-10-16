#!/usr/bin/env python3
"""Clean release reproduction and boundary controls; never reseal reviewed files."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import tempfile
import warnings
import zipfile

OWN=Path(__file__).resolve().parent
ROOT=OWN.parents[3]
RELEASE=OWN.parent/'kn-minus-edge-release'
ARCHIVE=ROOT/'output/release/r027-complete-graph-minus-edge-v1.zip'
MH='57976ac06388e96eef4db967570b3bf1327a798c029d32e40b568d1744ac46f7'
GH='4ad794eb1dc7957b71da3b060085a901f3e391384366b3e1de2da7be5b90e70e'
AH='a98ee88f40ab1f935a285fad0a179487d5fe36a54cd0e73bc15b5d833b3aa481'
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
    assert sha(ARCHIVE.read_bytes())==AH
    results=[]
    def run(label,args,expected=0,cwd=None):
        r=subprocess.run(['python3','-B',*map(str,args)],cwd=cwd,capture_output=True,text=True)
        results.append(dict(label=label,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
        assert r.returncode==expected and 'Traceback' not in r.stderr,(label,r.stderr)
        return r
    def verify(label,path,mh=MH,gh=GH,expected=0):
        return run(label,[RELEASE/'verify_bundle.py',path,'--manifest-sha256',mh,'--gate-sha256',gh],expected)
    verify('original ZIP',ARCHIVE)
    with tempfile.TemporaryDirectory(prefix='crossing-final-') as tmp:
        d=Path(tmp);clean=d/'clean'
        with zipfile.ZipFile(ARCHIVE) as z:z.extractall(clean)
        before={p.relative_to(clean).as_posix():sha(p.read_bytes()) for p in clean.rglob('*') if p.is_file()}
        verify('clean extraction',clean)
        base=clean/'frontier/campaigns/2026-10-14'
        run('standalone manuscript public mode',[base/'kn-minus-edge-manuscript-r2/support/verify_package.py','--public','--manifest-sha256','69a130a3e5d199277c2c7105b4e51c7a0fba972d7614aab86cc30236f515ac53'],cwd=d)
        run('formal payload only',[base/'kn-minus-edge-formal-v1/verify.py','--payload-only'],cwd=d)
        run('portable compiler/dependency/source setup',[clean/'rebuild_formal.py','--root',clean,'--lean',ROOT.parent/'dlp-research/.tools/lean-4.34.1-linux/bin/lean','--cache',OWN.parent/'formal/.lake/packages','--check-setup'],cwd=d)
        run('deterministic reassembly',[clean/'assemble.py','--gate',clean/'FINAL-GATE.json','--gate-sha256',GH,'--output',d/'reassembled.zip'],cwd=d)
        assert (d/'reassembled.zip').read_bytes()==ARCHIVE.read_bytes()
        verify('wrong manifest anchor',ARCHIVE,'0'*64,expected=1)
        verify('wrong gate anchor',ARCHIVE,gh='0'*64,expected=1)
        target=clean/'README.md';old=target.read_bytes();target.write_bytes(old+b'changed')
        verify('tampered payload',clean,expected=1);target.write_bytes(old)
        target.unlink();verify('missing payload',clean,expected=1);target.write_bytes(old)
        extra=clean/'unlisted';extra.write_text('extra');verify('extra payload',clean,expected=1);extra.unlink()
        target.unlink();target.symlink_to(d/'outside');verify('dangling symlink',clean,expected=1);target.unlink();target.write_bytes(old)
        for label,name in [('duplicate ZIP','README.md'),('traversal ZIP','../escape')]:
            bad=d/(label.replace(' ','-')+'.zip');shutil.copy2(ARCHIVE,bad)
            with warnings.catch_warnings():
                warnings.simplefilter('ignore')
                with zipfile.ZipFile(bad,'a') as z:z.writestr(name,b'bad')
            verify(label,bad,expected=1)
        assert before=={p.relative_to(clean).as_posix():sha(p.read_bytes()) for p in clean.rglob('*') if p.is_file()}
        verify('restored extraction',clean)
    result=dict(status='PASS_FINAL_PACKAGE',archive=str(ARCHIVE.relative_to(ROOT)),bytes=ARCHIVE.stat().st_size,
                sha256=AH,manifest_sha256=MH,gate_sha256=GH,files=len(before),
                verifier_sha256=sha((RELEASE/'verify_bundle.py').read_bytes()),
                bundle_common_sha256=sha((RELEASE/'bundle_common.py').read_bytes()),
                unchanged_extracted_files=len(before),deterministic_archive_byte_identical=True,runs=results,
                fresh_build='Prior release-fresh-formal.json: fresh source build PASS; this run validates exact same payload and pinned setup from extraction without redundant compilation.',
                full_crossing_formalized=False,published=False,scope='Integrity and reproduction, not a new proof or priority review.')
    (OWN/'final-package-verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='runs'},indent=2))

if __name__=='__main__':main()
