"""Reason-checked copied-package controls, with optional copied finite replay."""
import argparse, hashlib, json, shutil, subprocess, tempfile
from pathlib import Path

def seal(p):
    m={'status':'author candidate; no independent verdict','files':{str(x.relative_to(p)):hashlib.sha256(x.read_bytes()).hexdigest() for x in sorted(p.rglob('*')) if x.is_file() and x.name!='MANIFEST.json'},'directories':sorted(str(x.relative_to(p)) for x in p.rglob('*') if x.is_dir())}
    (p/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
    return hashlib.sha256((p/'MANIFEST.json').read_bytes()).hexdigest()
def main(root,expected,tree,replay):
    out=[]
    with tempfile.TemporaryDirectory(prefix='t314c-controls-',dir='/var/tmp') as tmp:
        base=Path(tmp)
        def trial(name,reason,mutate=None,reseal=False,anchor=None):
            p=base/name;shutil.copytree(root,p)
            if mutate:mutate(p)
            h=seal(p) if reseal else expected
            if anchor is not None:h=anchor
            r=subprocess.run(['python','-B',str(p/'verify.py'),'--expected',h,'--tree',str(tree)],capture_output=True,text=True)
            assert r.returncode!=0 and r.stdout.strip()=='REJECT: '+reason,(name,r.stdout,r.stderr)
            out.append({'control':name,'rejection':reason})
        trial('wrong-anchor','MANIFEST_ANCHOR',anchor='0'*64)
        trial('none-anchor','EXPECTED_ANCHOR',anchor='None')
        trial('missing','FILE_MEMBERSHIP',lambda p:(p/'candidate.md').unlink())
        trial('extra','FILE_MEMBERSHIP',lambda p:(p/'forged-pass.txt').write_text('PASS'))
        trial('extra-directory','DIRECTORY_MEMBERSHIP',lambda p:(p/'unexpected').mkdir())
        trial('changed-proof','PAYLOAD_HASH',lambda p:(p/'candidate.md').write_text('unreviewed replacement'))
        trial('symlink','SYMLINK',lambda p:(p/'external-link').symlink_to(tree))
        def change_json(p,file,key,value):
            j=json.loads((p/file).read_text());j[0][key]=value;(p/file).write_text(json.dumps(j))
        trial('source-claim','SOURCE_CANONICAL',lambda p:change_json(p,'source-receipts.json','git_blob','0'*40),True)
        trial('source-url','SOURCE_URL',lambda p:change_json(p,'source-receipts.json','url','https://example.invalid/'),True)
        trial('source-bytes','SOURCE_GIT',lambda p:(p/'private/README.md').write_text('replacement'),True)
        trial('source-sha','SOURCE_SHA',lambda p:change_json(p,'source-receipts.json','sha256','0'*64),True)
        trial('scope-reseal','SCOPE_ANCHOR',lambda p:(p/'original-scope.md').write_text('weakened scope'),True)
        trial('primary-receipt','PRIMARY_SHA',lambda p:change_json(p,'primary-receipts.json','sha256','0'*64),True)
        # Root manifest edits cannot be accepted under the external original anchor.
        trial('resealed-proof','MANIFEST_ANCHOR',lambda p:((p/'candidate.md').write_text('forged PASS'),seal(p)))
        if replay:
            p=base/'replay';shutil.copytree(root,p)
            r=subprocess.run(['python','-B',str(p/'diagnostics.py')],capture_output=True,text=True,check=True)
            assert json.loads(r.stdout)==json.loads((p/'diagnostic-results.json').read_text())
    return {'reason_checked_controls':out,'count':len(out),'copied_finite_replay':bool(replay),'limits':'copied integrity controls and finite implementation checks, not independent review'}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--expected',required=True);ap.add_argument('--tree',type=Path,required=True);ap.add_argument('--replay',action='store_true');a=ap.parse_args()
    print(json.dumps(main(Path(__file__).resolve().parent,a.expected,a.tree,a.replay),indent=2,sort_keys=True))
