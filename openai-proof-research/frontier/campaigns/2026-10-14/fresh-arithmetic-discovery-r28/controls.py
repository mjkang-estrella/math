#!/usr/bin/env python3
"""Copied adversarial integrity checks; writes only /var/tmp copies. MIT."""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--verifier-sha256',required=True);a=ap.parse_args()
    base=Path(__file__).resolve().parent
    if sha(base/'manifest.json')!=a.manifest_sha256 or sha(base/'verify.py')!=a.verifier_sha256:raise SystemExit('external anchor mismatch before controls')
    cases=['positive','public_only_positive','wrong_manifest_anchor','wrong_verifier_anchor','edit_proof','delete_proof','extra_public','symlink','edit_manifest','edit_verifier','edit_private','extra_private','extra_empty_directory','root_symlink','ancestor_symlink','hardlink','fifo','nested_manifest','self_reseal']
    out=[]
    for case in cases:
        with tempfile.TemporaryDirectory(prefix='t008m-controls-',dir='/var/tmp') as temp:
            parent=Path(temp);real=parent/'real';real.mkdir();d=real/'packet';shutil.copytree(base,d)
            invocation=d;ma=a.manifest_sha256;va=a.verifier_sha256;private=True
            if case=='public_only_positive':shutil.rmtree(d/'private');private=False
            elif case=='wrong_manifest_anchor':ma='0'*64
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
            elif case=='extra_empty_directory':(d/'unlisted-empty').mkdir()
            elif case=='root_symlink':
                invocation=parent/'root-link';invocation.symlink_to(d,target_is_directory=True)
            elif case=='ancestor_symlink':
                link=parent/'ancestor-link';link.symlink_to(real,target_is_directory=True);invocation=link/'packet'
            elif case=='hardlink':os.link(d/'candidate-008.md',parent/'external-hardlink')
            elif case=='fifo':os.mkfifo(d/'unlisted-fifo')
            elif case=='nested_manifest':(d/'provenance'/'manifest.json').write_text('{}\n')
            elif case=='self_reseal':
                p=d/'candidate-008.md';p.write_text('altered\n');mp=d/'manifest.json';m=json.loads(mp.read_text());m['public']['candidate-008.md']={'sha256':sha(p),'bytes':p.stat().st_size};mp.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
            command=[sys.executable,str(invocation/'verify.py'),'--manifest-sha256',ma,'--verifier-sha256',va]
            if private:command.append('--private')
            p=subprocess.run(command,capture_output=True,text=True,timeout=20)
            expected=case in ['positive','public_only_positive']
            if (p.returncode==0)!=expected:raise AssertionError((case,p.returncode,p.stdout,p.stderr))
            out.append({'case':case,'expected_accept':expected,'exit_code':p.returncode,'passed':True,'message':(p.stdout+p.stderr).strip()})
    print(json.dumps({'status':'PASS_COPIED_CONTROLS_NOT_PROOF','cases':out},indent=2))
if __name__=='__main__':main()
