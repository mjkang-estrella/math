#!/usr/bin/env python3
"""Copied positive/adversarial verifier controls. MIT. Source packet is read-only."""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--expected-manifest',required=True);ap.add_argument('--expected-verifier',required=True);a=ap.parse_args()
    root=Path(os.path.abspath(__file__)).parent
    results={}
    with tempfile.TemporaryDirectory(prefix='t047n-controls-',dir='/var/tmp') as td:
        td=Path(td)
        names=['positive','public_only','wrong_manifest','wrong_verifier','edit_proof','delete_proof','extra_file','extra_empty_dir','nested_manifest','root_symlink','ancestor_symlink','hardlink','fifo','edit_manifest','edit_verifier','edit_private','extra_private','self_reseal']
        for name in names:
            c=td/name;shutil.copytree(root,c);invoke=c;extra=[];mh=a.expected_manifest;vh=a.expected_verifier
            if name=='public_only':shutil.rmtree(c/'private');extra=['--public-only']
            if name=='wrong_manifest':mh='0'*64
            if name=='wrong_verifier':vh='0'*64
            if name=='edit_proof':
                with (c/'candidate-047.md').open('a') as f:f.write('\nmutation\n')
            if name=='delete_proof':(c/'candidate-047.md').unlink()
            if name=='extra_file':(c/'extra.txt').write_text('extra')
            if name=='extra_empty_dir':(c/'empty').mkdir()
            if name=='nested_manifest':
                (c/'nested').mkdir();(c/'nested/manifest.json').write_text('{}')
            if name=='root_symlink':
                invoke=td/'root-link';invoke.symlink_to(c,target_is_directory=True)
            if name=='ancestor_symlink':
                holder=td/'holder';holder.mkdir();shutil.move(str(c),str(holder/'packet'));link=td/'holder-link';link.symlink_to(holder,target_is_directory=True);invoke=link/'packet'
            if name=='hardlink':os.link(c/'candidate-047.md',c/'duplicate-hardlink')
            if name=='fifo':os.mkfifo(c/'fifo')
            if name=='edit_manifest':
                with (c/'manifest.json').open('a') as f:f.write(' ')
            if name=='edit_verifier':
                with (c/'verify.py').open('a') as f:f.write('\n# mutation\n')
            if name=='edit_private':next((c/'private/source047').glob('*.tex')).write_text('mutation')
            if name=='extra_private':(c/'private/extra').write_text('extra')
            if name=='self_reseal':
                p=c/'candidate-047.md';p.write_text(p.read_text()+'\nmutation\n');m=json.loads((c/'manifest.json').read_text());m['files']['candidate-047.md']={'bytes':p.stat().st_size,'sha256':sha(p)};(c/'manifest.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n')
            cmd=[sys.executable,str(invoke/'verify.py'),'--expected-manifest',mh,'--expected-verifier',vh,*extra]
            p=subprocess.run(cmd,capture_output=True,text=True,timeout=20)
            ok=(p.returncode==0) if name in ['positive','public_only'] else (p.returncode!=0)
            if not ok:raise AssertionError(name+': '+p.stdout+p.stderr)
            results[name]='PASS'
    print(json.dumps({'status':'PASS_ALL_COPIED_CONTROLS','cases':results},sort_keys=True,indent=2))
if __name__=='__main__':main()
