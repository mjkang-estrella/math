#!/usr/bin/env python3
"""Preparatory identity/refusal tests only; no synthetic r2 or final archive. MIT."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import zipfile
from release_common import *
from final_release import verify, BUNDLE
HERE=Path(__file__).absolute().parent

def main():
    work=Path(tempfile.mkdtemp(prefix='t212m-release-draft-',dir='/var/tmp'))
    ia=sha(read(HERE,'IMPLEMENTATION-MANIFEST.json'));stage=work/'stage';events=[]
    def run(label,argv,success):
        r=subprocess.run([sys.executable,'-B',*map(str,argv)],capture_output=True,text=True)
        require((r.returncode==0)==success,label+' unexpected outcome: '+r.stdout+r.stderr)
        events.append({'test':label,'expected_success':success,'exit_code':r.returncode,
                       'stdout':r.stdout,'stderr':r.stderr})
        return r
    common=[HERE/'final_release.py']
    run('102 selected identities',[*common,'preflight','--implementation-anchor',ia,'--campaign',HERE.parent],True)
    result=run('preparatory stage',[*common,'stage','--implementation-anchor',ia,'--campaign',HERE.parent,'--output',stage],True)
    ma=json.loads(result.stdout)['bundle_manifest_sha256']
    run('standalone stage verification',[stage/'final_release.py','verify','--implementation-anchor',ia,'--manifest-anchor',ma,'--input',stage],True)
    for extra in ([],['--r2-anchor','0'*64,'--closure-anchor','1'*64]):
        out=work/('forbidden-final-'+str(len(extra))+'.zip')
        run('pending completion refuses final '+str(len(extra)),[*common,'assemble','--implementation-anchor',ia,'--campaign',HERE.parent,'--output',out,*extra],False)
        require(not out.exists(),'refusal emitted archive')
    data,ds=tree(stage)
    def refuse(label,fn):
        try:fn()
        except (ValueError,OSError,KeyError,TypeError,zipfile.BadZipFile) as e:
            events.append({'test':label,'expected_success':False,'exception':type(e).__name__,'reason':str(e)});return
        raise ValueError('unexpected acceptance: '+label)
    refuse('wrong external implementation anchor',lambda:verify(data,ds,ma,'0'*64))
    refuse('wrong external bundle anchor',lambda:verify(data,ds,'0'*64,ia))
    for name in ('release-policy.json','public-selection-final-draft.json','release_common.py',
                 't212m-formal-review-r1/independent-logs/Independent.lean.log'):
        bad=dict(data);bad[name]+=b'\n'
        refuse('modified '+name,lambda:verify(bad,ds,ma,ia))
    bad=dict(data);del bad['t212m-formal-review-r1/independent-logs/Independent.lean.log']
    refuse('missing independent log',lambda:verify(bad,ds,ma,ia))
    bad=dict(data);bad['extra.txt']=b'x'
    refuse('extra file',lambda:verify(bad,ds,ma,ia))
    refuse('empty directory',lambda:verify(data,sorted(ds+['empty']),ma,ia))
    refuse('final flag cannot promote draft',lambda:verify(data,ds,ma,ia,True,'0'*64,'1'*64))
    refuse('duplicate JSON key',lambda:parse(b'{"x":1,"x":2}'))
    for name in ('../x','/x','a//b','a/./b','a\\b','private/body.tex','.lake/a.olean'):
        refuse('unsafe/private name '+name,lambda:public(name))
    link=work/'linked-stage';link.symlink_to(stage,target_is_directory=True)
    refuse('linked root',lambda:tree(link))
    refuse('linked ancestor',lambda:read(link,'README.md'))
    for kind in ('symlink','hardlink','fifo'):
        tmp=work/('bad-'+kind);tmp.mkdir();dest=tmp/'entry'
        if kind=='symlink':dest.symlink_to(stage/'README.md')
        elif kind=='hardlink':os.link(stage/'README.md',dest)
        else:os.mkfifo(dest)
        refuse(kind+' tree entry',lambda:tree(tmp))
        dest.unlink()
    refuse('output overlap',lambda:new_output(stage/'new-output',[stage]))
    refuse('existing output',lambda:new_output(stage,[HERE]))
    # Toy archives only: never synthesize a review or emit a final T212M archive.
    toy={'a.txt':b'example','nested/b.txt':b'deterministic bytes'}
    z1=work/'toy-1.zip';z2=work/'toy-2.zip';stable_zip(z1,toy);stable_zip(z2,toy)
    require(z1.read_bytes()==z2.read_bytes() and zip_payload(z1)==toy,'toy deterministic ZIP failure')
    events.append({'test':'toy-only deterministic canonical ZIP','expected_success':True,'sha256':sha(z1.read_bytes())})
    for label,names in (('traversal',['../x']),('duplicates',['x','x'])):
        z=work/(label+'.zip')
        with zipfile.ZipFile(z,'x') as f:
            for n in names:f.writestr(n,b'x')
        refuse('unsafe ZIP '+label,lambda:zip_payload(z))
    z=work/'symlink.zip'
    with zipfile.ZipFile(z,'x') as f:
        i=zipfile.ZipInfo('link',(2026,10,18,0,0,0));i.create_system=3;i.external_attr=0o120777<<16
        f.writestr(i,b'target',compress_type=zipfile.ZIP_DEFLATED)
    refuse('ZIP symbolic-link metadata',lambda:zip_payload(z))
    run('standalone replay rejects wrong anchor before tools/output',
        [stage/'replay_release.py','original','--implementation-anchor','0'*64,
         '--manifest-anchor',ma,'--output',work/'no-replay'],False)
    require(not (work/'no-replay').exists(),'refused replay wrote output')
    result={'status':'PASS_PREPARATORY_IDENTITY_AND_REFUSAL_TESTS','implementation_anchor':ia,
            'stage_manifest_anchor':ma,'work_directory':str(work),'test_count':len(events),
            'tests':events,'final_archive_created':False,'r2_evidence_fabricated':False,
            'pdf_lean_replayed_by_this_test':False,'accepted':False,'published':False}
    out=HERE/'draft-release-tests-v2.json';require(not out.exists(),'new receipt required')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='tests'},indent=2))
if __name__=='__main__':main()
