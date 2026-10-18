#!/usr/bin/env python3
"""Mutate temporary PUBLIC copies only. The original packet is read-only."""
import argparse, hashlib, json, shutil, subprocess, sys, tempfile
from pathlib import Path

def run(root,anchor):
    original=json.loads((root/'MANIFEST.json').read_text());results=[]
    cases=['payload_edit','payload_missing','extra_public_body','external_manifest_edit','reanchored_scope_edit','forged_independent_pass','forged_acceptance','module_receipt_edit']
    for case in cases:
        with tempfile.TemporaryDirectory(prefix='r103-control-',dir='/var/tmp') as td:
            d=Path(td)
            for n in [*original['files'],'MANIFEST.json']:
                (d/n).parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/n,d/n)
            expected=anchor;reason=''
            if case=='payload_edit':
                with (d/'candidate-proof.md').open('a') as f:f.write('\nMUTATION\n')
                reason='payload hash mismatch'
            elif case=='payload_missing':(d/'single-jump-replacement.md').unlink();reason='public inventory mismatch'
            elif case=='extra_public_body':(d/'UNSELECTED-PRIMARY.txt').write_text('synthetic forbidden extra payload');reason='public inventory mismatch'
            elif case=='external_manifest_edit':
                with (d/'MANIFEST.json').open('a') as f:f.write(' ')
                reason='external manifest anchor mismatch'
            else:
                m=json.loads((d/'MANIFEST.json').read_text())
                if case=='reanchored_scope_edit':
                    n='scope-status.json';s=json.loads((d/n).read_text());s['target']='weakened FDD-only target';(d/n).write_text(json.dumps(s));m['files'][n]=hashlib.sha256((d/n).read_bytes()).hexdigest();reason='frozen scope anchor mismatch'
                elif case=='forged_independent_pass':m['independent_gates']['proof']='PASS_FULL';reason='independent gates must remain pending'
                elif case=='forged_acceptance':m['accepted']=True;reason='acceptance/publication/count forbidden'
                else:
                    n='author-assembly-status.json';s=json.loads((d/n).read_text());s['modules']['candidate-proof.md']='0'*64;(d/n).write_text(json.dumps(s));m['files'][n]=hashlib.sha256((d/n).read_bytes()).hexdigest();reason='module anchor mismatch'
                (d/'MANIFEST.json').write_text(json.dumps(m,sort_keys=True));expected=hashlib.sha256((d/'MANIFEST.json').read_bytes()).hexdigest()
            r=subprocess.run([sys.executable,str(root/'verify.py'),'--root',str(d),'--manifest-sha256',expected],capture_output=True,text=True)
            assert r.returncode!=0 and reason in r.stderr,(case,r.stdout,r.stderr)
            results.append({'case':case,'rejected_for':reason})
    return {'status':'PASS_COPIED_NEGATIVE_CONTROLS_ONLY','controls':results,'original_mutated':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--manifest-sha256',required=True);a=p.parse_args();print(json.dumps(run(a.root,a.manifest_sha256),indent=2))
