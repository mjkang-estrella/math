#!/usr/bin/env python3
"""MIT. Disposable copied-packet controls; does not mutate sealed payloads."""
import argparse, hashlib, importlib.util, json, os, shutil
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--scratch',type=Path,required=True);a=p.parse_args()
    root=a.root.absolute();scratch=a.scratch.absolute()
    # Scratch must be a new, uniquely assigned sibling inside the owned r49/checks.
    assert scratch.parent==root/'checks' and not scratch.exists()
    scratch.mkdir()
    spec=importlib.util.spec_from_file_location('r49_verifier',root/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
    anchor=hashlib.sha256((root/'MANIFEST.json').read_bytes()).hexdigest();results=[]
    def fresh(name):
        dest=scratch/name
        shutil.copytree(root,dest,ignore=lambda p,n:[scratch.name] if Path(p)==scratch.parent else [])
        return dest
    def run(name,mutation=None,wrong=False,rootlink=False):
        dest=fresh(name)
        if mutation:mutation(dest)
        if rootlink:
            link=scratch/(name+'-link');link.symlink_to(dest,target_is_directory=True);dest=link
        try:v.check(dest,'0'*64 if wrong else anchor);accepted=True;reason='PASS'
        except Exception as e:accepted=False;reason=str(e)
        expected=name=='positive_copy'
        assert accepted==expected,(name,accepted,reason)
        results.append({'case':name,'expected':'accept' if expected else 'reject','actual':reason})
    try:
        run('positive_copy')
        run('wrong_anchor',wrong=True)
        run('changed_payload',lambda d:(d/'report.md').write_bytes((d/'report.md').read_bytes()+b'changed\n'))
        run('changed_scope_status',lambda d:(d/'original-scope.txt').write_bytes((d/'original-scope.txt').read_bytes()+b'changed\n'))
        run('missing_payload',lambda d:(d/'report.md').unlink())
        run('extra_file',lambda d:(d/'extra.txt').write_text('extra'))
        run('extra_empty_directory',lambda d:(d/'extra-empty').mkdir())
        run('root_symlink',rootlink=True)
        def payload_link(d):
            (d/'report.md').unlink();(d/'report.md').symlink_to('checkpoint.md')
        run('payload_symlink',payload_link)
        def hardlink(d):
            (d/'report.md').unlink();os.link(d/'checkpoint.md',d/'report.md')
        run('payload_hardlink',hardlink)
        run('fifo',lambda d:os.mkfifo(d/'fifo'))
        run('nested_manifest',lambda d:(d/'checks'/'MANIFEST.json').write_text('{}'))
        def reseal(d):
            f=d/'report.md';f.write_bytes(f.read_bytes()+b'changed\n');m=json.loads((d/'MANIFEST.json').read_text())
            for e in m['files']:
                if e['path']=='report.md':e['bytes']=f.stat().st_size;e['sha256']=hashlib.sha256(f.read_bytes()).hexdigest()
            (d/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
        run('self_resealed_wrong_external_anchor',reseal)
    finally:shutil.rmtree(scratch)
    return {'status':'PASS','controls':results,'scope':'Copied intermediate packet, before adding this result and final verification record. Final sealed positive/wrong-anchor checks run separately. No mathematical claims.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
