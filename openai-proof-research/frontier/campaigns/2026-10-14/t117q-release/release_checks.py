#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Pending-release controls on disposable copies; no compiler or archive creation."""
import copy,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
from bundle_common import EXPECTED_ANCHORS,parse,sha
HERE=Path(__file__).resolve().parent
ROOT=HERE if (HERE/'frontier').is_dir() else HERE.parents[3]
PREFIX='frontier/campaigns/2026-10-14/'

def main():
    work=Path(tempfile.mkdtemp(prefix='t117q-release-controls-',dir='/var/tmp'))
    copied=work/PREFIX/'t117q-release';copied.parent.mkdir(parents=True)
    shutil.copytree(HERE,copied)
    selection=parse((HERE/'payload-selection.json').read_bytes())
    for row in selection['files']:
        p=work/row['path'];p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/row['path'],p)
    results=[]
    def run(case,argv,accept,reason):
        p=subprocess.run([sys.executable,'-B']+list(map(str,argv)),capture_output=True,text=True,cwd=work)
        output=p.stdout+p.stderr
        assert (p.returncode==0)==accept and reason in output,(case,p.returncode,output)
        results.append(dict(case=case,accepted=p.returncode==0,expected_reason=reason))
    run('positive-preparation',[copied/'verify_preparation.py'],True,'PREPARATION IDENTITIES VERIFIED: 66')
    prep=parse((copied/'preparation.json').read_bytes())
    def assemble(case,gate,reason,badhash=False):
        f=work/(case+'.json');raw=(json.dumps(gate,indent=2)+'\n').encode();f.write_bytes(raw)
        out=work/(case+'.zip')
        run(case,[copied/'assemble.py','--gate',f,'--gate-sha256','0'*64 if badhash else sha(raw),'--output',out],False,reason)
        assert not out.exists(),'guard wrote archive'
    assemble('pending-gate',prep,'final independent gate still pending')
    forged=copy.deepcopy(prep);forged.update(status='ALL_REVIEW_GATES_PASS',artifacts=[selection['files'][0]])
    forged['verdicts']['manuscript']='PASS_FULL_MANUSCRIPT_T117Q'
    assemble('forged-all-gates-pass',forged,'independent review anchors not yet adopted')
    fake=copy.deepcopy(forged);fake['anchors']['t117q-manuscript-review-r1']={'file':'manifest.json','sha256':'0'*64}
    assemble('forged-manuscript-anchor',fake,'independent review anchors not yet adopted')
    assemble('wrong-external-gate-hash',forged,'external gate hash mismatch',True)
    fake=copy.deepcopy(forged);fake['full_T117Q_formalized']=True
    assemble('false-full-formalization',fake,'unsupported full formal claim')
    fake=copy.deepcopy(forged);fake['scope_sha256']='0'*64
    assemble('changed-scope',fake,'frozen scope changed')
    for packet,entry in EXPECTED_ANCHORS.items():
        if entry is None:continue
        target=work/PREFIX/packet/entry['file'];raw=target.read_bytes()
        target.write_bytes(raw+b' ')
        run('changed-anchor-'+packet,[copied/'verify_preparation.py'],False,'external packet anchor mismatch: '+packet)
        target.write_bytes(raw)
    target=work/selection['files'][0]['path'];raw=target.read_bytes();target.unlink()
    run('missing-selected-file',[copied/'verify_preparation.py'],False,'PREPARATION REFUSED:')
    target.write_bytes(raw+b' ')
    run('changed-selected-file',[copied/'verify_preparation.py'],False,'size/hash mismatch:')
    target.unlink();target.symlink_to(work/'pending-gate.json')
    run('symlink-selected-file',[copied/'verify_preparation.py'],False,'symlink:')
    target.unlink();target.write_bytes(raw)
    sibling=work/'hardlink-target';sibling.write_bytes(raw)
    target.unlink();os.link(sibling,target)
    run('hardlink-selected-file',[copied/'verify_preparation.py'],False,'hardlinked file:')
    target.unlink();target.write_bytes(raw)
    selpath=copied/'payload-selection.json';original_selection=selpath.read_bytes()
    for case,component in [('private-selected-path','private'),('cache-selected-path','.lake')]:
        altered=copy.deepcopy(selection)
        altered['files'][0]['path']=PREFIX+'t117q-manuscript-v1/'+component+'/unlicensed.pdf'
        selpath.write_text(json.dumps(altered))
        run(case,[copied/'verify_preparation.py'],False,'private/cache payload forbidden')
    selpath.write_bytes(original_selection)
    run('restored-preparation',[copied/'verify_preparation.py'],True,'PREPARATION IDENTITIES VERIFIED: 66')
    # Exercise the portable verifier's pending-gate boundary directly, without a ZIP.
    script=work/'portable-pending.py'
    script.write_text('import sys\nsys.dont_write_bytecode=True\nsys.path.insert(0,'+repr(str(copied))+')\nfrom bundle_common import gate_check,parse\ngate_check(parse(open('+repr(str(work/'forged-all-gates-pass.json'))+',"rb").read()))\n')
    run('portable-pending-guard',[script],False,'independent review anchors not yet adopted')
    print(json.dumps(dict(status='PASS_PREPARATION_CONTROLS_ONLY',work_directory=str(work),results=results,archive_created=False,compiler_replayed=False,independent_review=False),indent=2))
if __name__=='__main__':main()
