#!/usr/bin/env python3
"""Development controls; original project code, MIT, Myeongjin Kang.
Requires a prepared copy and external anchor. Writes only to a fresh --output.
No synthetic manuscript PASS is created. Actual NEEDS_REVISION r3 is a negative control.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

HERE = Path(__file__).absolute().parent
namespace = {'__file__': str(HERE/'release.py'), '__name__': 'release_controls_import'}
exec(compile((HERE/'release.py').read_bytes(), str(HERE/'release.py'), 'exec'), namespace)
r = type('Release', (), namespace)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--prepared',type=Path,required=True)
    p.add_argument('--anchor',required=True)
    p.add_argument('--review-r3',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    out=r.new_output(a.output,[a.prepared,a.review_r3,HERE/'templates']);out.mkdir()
    mf,payload=r.verify(a.prepared,a.anchor)
    rows=[]
    def reject(label, fn):
        try: fn()
        except (ValueError, OSError, KeyError, zipfile.BadZipFile) as error:
            rows.append({'control':label,'status':'EXPECTED_REJECTION','reason':str(error)})
        else: raise AssertionError('control accepted: '+label)
    def clone(label):
        dest=out/label;shutil.copytree(a.prepared,dest);return dest
    reject('wrong-bundle-anchor',lambda:r.verify(a.prepared,'0'*64))
    broken=clone('modified');(broken/'README.md').write_text('tampered')
    reject('modified-file',lambda:r.verify(broken,a.anchor))
    extra=clone('extra');(extra/'extra.txt').write_text('extra')
    reject('extra-file',lambda:r.verify(extra,a.anchor))
    missing=clone('missing');(missing/'README.md').unlink()
    reject('missing-file',lambda:r.verify(missing,a.anchor))
    directory=clone('directory');(directory/'empty').mkdir()
    reject('extra-empty-directory',lambda:r.verify(directory,a.anchor))
    linked=clone('linked');(linked/'README.md').unlink();(linked/'README.md').symlink_to(a.prepared/'README.md')
    reject('symlink-payload',lambda:r.verify(linked,a.anchor))
    linked_root=out/'linked-root';linked_root.symlink_to(a.prepared,target_is_directory=True)
    reject('symlink-root',lambda:r.verify(linked_root,a.anchor))
    # Rehashing modified bytes internally does not replace an external anchor.
    altered=dict(payload);altered['README.md']=b'changed'
    altered['MANIFEST.json']=r.manifest({n:b for n,b in altered.items() if n!='MANIFEST.json'},'PREPARATION_ONLY')
    reject('rehash-without-external-anchor',lambda:r.validate_bytes(altered,a.anchor))
    for name in ['../escape','/absolute','a\\b','a/./b','a//b','C:drive','CON.txt','a.','a\nnewline']:
        reject('unsafe-path:'+repr(name),lambda name=name:r.safe(name))
    reject('third-party-pdf-name',lambda:r.public('sources/third-party.pdf'))
    reject('duplicate-json-key',lambda:r.parse(b'{"x":1,"x":2}'))
    reject('output-inside-input',lambda:r.new_output(a.prepared/'nested',[a.prepared]))
    reject('output-reuse',lambda:r.new_output(out,[a.prepared]))
    zip1=out/'preparation-1.zip';zip2=out/'preparation-2.zip'
    r.stable_zip(zip1,payload);r.stable_zip(zip2,payload)
    assert zip1.read_bytes()==zip2.read_bytes()
    archive_hash=r.sha(zip1.read_bytes())
    assert r.zip_payload(zip1,archive_hash)==payload
    rows.append({'control':'deterministic-preparation-archive','status':'PASS','archive_sha256':archive_hash})
    reject('wrong-archive-anchor',lambda:r.zip_payload(zip1,'0'*64))
    def unsafe_zip(label,names,mode=0o100644):
        dest=out/(label+'.zip')
        with zipfile.ZipFile(dest,'x') as z:
            for name in names:
                info=zipfile.ZipInfo(name,(2026,10,18,0,0,0));info.create_system=3
                info.external_attr=mode<<16;info.compress_type=zipfile.ZIP_DEFLATED
                z.writestr(info,b'bad')
        return dest
    for label,names,mode in [('traversal',['../escape'],0o100644),('absolute',['/escape'],0o100644),('symlink',['linked'],0o120777),('duplicate',['dup','dup'],0o100644),('order',['z','a'],0o100644)]:
        archive=unsafe_zip(label,names,mode)
        rejected_output=out/('extract-'+label)
        args=type('Args',(),dict(archive=archive,archive_sha256=r.sha(archive.read_bytes()),anchor=a.anchor,output=rejected_output))
        reject('unsafe-extraction:'+label,lambda args=args:r.extract(args))
        assert not rejected_output.exists()
    # A canonical archive with an extra file fails exact membership before extraction.
    archive=out/'extra-member.zip';r.stable_zip(archive,{**payload,'extra.txt':b'extra'})
    rejected_output=out/'extract-extra'
    args=type('Args',(),dict(archive=archive,archive_sha256=r.sha(archive.read_bytes()),anchor=a.anchor,output=rejected_output))
    reject('unsafe-extraction:extra-member',lambda:r.extract(args));assert not rejected_output.exists()
    # This policy describes only the real, completed r3 negative fixture, never r4.
    review_anchor='9681947da10c149d4a3f5fec6362a317cef36e022c47703b2d88b7d6449e7e0d'
    policy={'schema':'t298p-review-layout-v1','review_anchor':review_anchor,
            'manuscript_anchor':r.MANUSCRIPT,'include':['review.md','verdict.json'],
            'report':'review.md','verdict':{'file':'verdict.json','pointer':'/verdict','pass_value':'PASS'},
            'required_findings':{'file':'verdict.json','pointer':'/required'},
            'manuscript_binding':{'file':'verdict.json','pointer':'/manuscript_manifest_sha256'}}
    raw=r.encoded(policy);pol=out/'r3-negative-control-policy.json';pol.write_bytes(raw)
    get=lambda n:r.read(a.review_r3,n)
    reject('wrong-review-anchor',lambda:r.review_gate(get,'0'*64,raw,r.sha(raw)))
    reject('wrong-policy-anchor',lambda:r.review_gate(get,review_anchor,raw,'0'*64))
    before=len(rows)
    reject('real-NEEDS_REVISION-r3',lambda:r.review_gate(get,review_anchor,raw,r.sha(raw)))
    assert rows[before]['reason']=='actual manuscript review did not PASS'
    args=type('Args',(),dict(prepared=a.prepared,preparation_anchor=a.anchor,output=out/'must-not-assemble',manuscript_review=a.review_r3,review_anchor=review_anchor,review_policy=pol,policy_anchor=r.sha(raw)))
    reject('assemble-real-NEEDS_REVISION-r3',lambda:r.assemble(args))
    assert not args.output.exists()
    args=type('Args',(),dict(prepared=a.prepared,preparation_anchor=a.anchor,output=out/'missing-gate',manuscript_review=None,review_anchor=None,review_policy=None,policy_anchor=None))
    reject('assemble-missing-review',lambda:r.assemble(args));assert not args.output.exists()
    # Execute the public extraction entrypoint, then the extracted verifier.
    extracted=out/'extracted'
    subprocess.run([sys.executable,'-I','-B',str(HERE/'release.py'),'extract','--archive',str(zip1),'--archive-sha256',archive_hash,'--anchor',a.anchor,'--output',str(extracted)],check=True)
    subprocess.run([sys.executable,'-I','-B',str(extracted/'release.py'),'verify','--bundle',str(extracted),'--anchor',a.anchor],check=True)
    rows.append({'control':'actual-clean-extraction-and-extracted-verifier','status':'PASS'})
    r.verify(a.prepared,a.anchor)
    receipt={'status':'PASS_DEVELOPMENT_CONTROLS','kind':'PREPARATION_ONLY','accepted':False,'count_change':0,'published':False,'full_theorem_formalized':False,'preparation_anchor':a.anchor,'controls':rows,'control_count':len(rows),'real_pass_gate_tested':False,'remaining_gate':'actual independently sealed manuscript-r2 PASS and parent-supplied policy'}
    (out/'controls-receipt.json').write_bytes(r.encoded(receipt))
    print(json.dumps({'status':receipt['status'],'controls':len(rows),'extracted':str(extracted),'archive_sha256':archive_hash}))

if __name__=='__main__':main()
