#!/usr/bin/env python3
"""Copied adversarial integrity checks; writes only temporary directories. MIT."""
import argparse,hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--verifier-sha256',required=True);a=ap.parse_args()
    base=Path(__file__).resolve().parent
    if sha(base/'manifest.json')!=a.manifest_sha256 or sha(base/'verify.py')!=a.verifier_sha256:raise SystemExit('external anchor mismatch before controls')
    cases=['positive','wrong_manifest_anchor','wrong_verifier_anchor','edit_proof','delete_proof','extra_public','symlink','edit_manifest','edit_verifier','edit_private','extra_private']
    out=[]
    with tempfile.TemporaryDirectory(prefix='t008m-controls-') as temp:
        for case in cases:
            d=Path(temp)/case;shutil.copytree(base,d)
            ma=a.manifest_sha256;va=a.verifier_sha256
            if case=='wrong_manifest_anchor':ma='0'*64
            elif case=='wrong_verifier_anchor':va='0'*64
            elif case=='edit_proof':(d/'candidate-008.md').write_text('altered\n')
            elif case=='delete_proof':(d/'candidate-008.md').unlink()
            elif case=='extra_public':(d/'unlisted.txt').write_text('extra\n')
            elif case=='symlink':(d/'unlisted-link').symlink_to('candidate-008.md')
            elif case=='edit_manifest':(d/'manifest.json').write_text('{}\n')
            elif case=='edit_verifier':
                p=d/'verify.py';p.write_text(p.read_text()+'\n# changed\n')
            elif case=='edit_private':
                p=next((d/'private').rglob('*.html'));p.write_text('changed\n')
            elif case=='extra_private':(d/'private'/'unlisted.txt').write_text('extra\n')
            p=subprocess.run([sys.executable,str(d/'verify.py'),'--manifest-sha256',ma,'--verifier-sha256',va,'--private'],capture_output=True,text=True)
            expected=case=='positive'
            if (p.returncode==0)!=expected:raise AssertionError((case,p.returncode,p.stdout,p.stderr))
            out.append({'case':case,'expected_accept':expected,'exit_code':p.returncode,'passed':True})
    print(json.dumps({'status':'PASS_COPIED_CONTROLS_NOT_PROOF','cases':out},indent=2))
if __name__=='__main__':main()
