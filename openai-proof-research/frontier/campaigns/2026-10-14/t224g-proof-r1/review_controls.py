#!/usr/bin/env python3
"""Copied positive and reason-checked negative controls for verify_review.py. Originals are never mutated."""
import argparse, hashlib, json, shutil, subprocess, sys, tempfile
from pathlib import Path
def sha(b):return hashlib.sha256(b).hexdigest()
def run(root,anchor,author):
    files=json.loads((root/'MANIFEST.json').read_text())['files'];out=[]
    cases=[('positive_copy',None),('payload_edit','review payload hash mismatch'),('payload_missing','review inventory mismatch'),
           ('extra_file','review inventory mismatch'),('wrong_anchor','external review manifest anchor mismatch'),
           ('forged_count','count/acceptance forbidden'),('upgraded_verdict','verdict field altered'),
           ('author_candidate_edit','author anchor mismatch: candidate-proof.md')]
    for case,reason in cases:
        with tempfile.TemporaryDirectory(prefix='t224g-review-ctl-',dir='/var/tmp') as td:
            d=Path(td)/'r';a=Path(td)/'a'
            for n in [*files,'MANIFEST.json']:(d/n).parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/n,d/n)
            shutil.copytree(author,a,ignore=shutil.ignore_patterns('private'))
            exp=anchor
            if case=='payload_edit':
                with (d/'review.md').open('a') as f:f.write('\nMUTATION\n')
            elif case=='payload_missing':(d/'reading-log.md').unlink()
            elif case=='extra_file':(d/'EXTRA.txt').write_text('x')
            elif case=='wrong_anchor':exp='0'*64
            elif case in('forged_count','upgraded_verdict'):
                s=json.loads((d/'review-status.json').read_text())
                if case=='forged_count':s['counted']=True
                else:s['verdict']='PASS_FULL_T224G';s['frozen_author_text']='PASS'
                (d/'review-status.json').write_text(json.dumps(s))
                m=json.loads((d/'MANIFEST.json').read_text());m['files']['review-status.json']=sha((d/'review-status.json').read_bytes())
                (d/'MANIFEST.json').write_text(json.dumps(m,sort_keys=True,indent=1));exp=sha((d/'MANIFEST.json').read_bytes())
            elif case=='author_candidate_edit':
                with (a/'candidate-proof.md').open('a') as f:f.write('\nMUTATION\n')
            r=subprocess.run([sys.executable,'-I','-B',str(root/'verify_review.py'),'--root',str(d),'--manifest-sha256',exp,'--author-root',str(a)],capture_output=True,text=True)
            if reason is None:assert r.returncode==0,(case,r.stderr);out.append({'case':case,'accepted':True})
            else:assert r.returncode!=0 and reason in r.stderr,(case,r.stdout,r.stderr);out.append({'case':case,'rejected_for':reason})
    return {'status':'PASS_COPIED_REVIEW_CONTROLS_ONLY','controls':out,'original_mutated':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    p.add_argument('--manifest-sha256',required=True);p.add_argument('--author-root',type=Path,required=True);a=p.parse_args()
    print(json.dumps(run(a.root,a.manifest_sha256,a.author_root),indent=1))
