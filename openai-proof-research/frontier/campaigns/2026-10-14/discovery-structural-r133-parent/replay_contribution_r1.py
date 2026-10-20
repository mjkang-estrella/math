#!/usr/bin/env python3
"""Parent artifact intake for T106O133 contribution review; no new mathematical verdict."""
import hashlib,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
FINAL='c2ec0773ab13d089bbb88bfe6100bfc40f27cb6f98d2233e2741c9a675d4db2b'
MANIFEST='9a795f7876886c5385618226c8434ee6c9a29f49c33a0472534229abe1510143'
REPORT='b8623cbc76f59a079b6edf162281d096cb71f182674f02dc17d0ee7cf2e86c94'
AUTHOR='28c1114b783e345e666741df7eadeecccdf6ae92aff898adf4a778b06624d832'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat();r=[s.st_mode,s.st_nlink]
        if stat.S_ISREG(s.st_mode):r += [s.st_size,sha(p)]
        elif stat.S_ISLNK(s.st_mode):r += [os.readlink(p)]
        out[p.relative_to(root).as_posix()]=r
    return out
def run(args,cwd):
    r=subprocess.run([sys.executable,'-B',*args],cwd=cwd,capture_output=True,text=True,
                     env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    return {'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
def main():
    parent=Path(__file__).resolve().parent;campaign=parent.parent;repo=campaign.parents[2]
    review=campaign/'t106o133-contribution-r1';author=campaign/'fresh-structural-discovery-r133'
    assert sha(review/'FINAL.json')==FINAL and sha(review/'packet/MANIFEST.json')==MANIFEST
    assert sha(review/'REPORT.md')==REPORT and sha(author/'FINAL.json')==AUTHOR
    fp=json.loads((review/'packet/public/input-fingerprints.json').read_text())
    contexts=list(fp['parent_inputs_used'])+['AGENTS.md','sources/upstream.json','sources/preprints-tree.json']
    before={'author':snapshot(author),'review':snapshot(review),'context':{n:sha(repo/n) for n in contexts}}
    tree={e['path']:e for e in json.loads((repo/'sources/preprints-tree.json').read_text())['tree']}
    receipts=json.loads((review/'packet/private/source/receipts.json').read_text())
    for r in receipts:
        e=tree[r['path']];p=review/'packet/private/source'/r['path'];data=p.read_bytes()
        assert e['type']=='blob' and r['size']==len(data)==e['size']
        assert r['git_blob_sha1']==e['sha']==hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert r['sha256']==hashlib.sha256(data).hexdigest()
        assert r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path']
    common=['--root','.', '--project',str(repo),'--finalhash',FINAL,'--author-finalhash',AUTHOR]
    original=run(['packet/public/verify.py',*common],review)
    with tempfile.TemporaryDirectory(prefix='contribution-r1-copy-',dir=parent) as td:
        copy=Path(td)/'review';shutil.copytree(review,copy,symlinks=True)
        verified=run(['packet/public/verify.py',*common],copy)
        bad=list(common);bad[bad.index('--finalhash')+1]='0'*64
        wrong=run(['packet/public/verify.py',*bad],copy)
        controls=run(['packet/public/controls.py',*common],copy)
        receipt=json.loads((copy/'artifact-controls.json').read_text())
    after={'author':snapshot(author),'review':snapshot(review),'context':{n:sha(repo/n) for n in contexts}}
    ok=(original['exit']==0 and verified['exit']==0 and wrong['exit']!=0
        and controls['exit']==0 and receipt['all_ok'] and before==after)
    man=json.loads((review/'packet/MANIFEST.json').read_text())['entries']
    out={'kind':'PARENT_ARTIFACT_INTAKE_ONLY','mathematical_gate':False,
         'detached_anchors':{'final':FINAL,'manifest':MANIFEST,'report':REPORT},
         'source_records_strictly_authenticated':len(receipts),
         'payload_files':sum(e['type']=='file' for e in man.values()),
         'directories_including_packet_root':sum(e['type']=='dir' for e in man.values()),
         'original_verify':original,'copied_verify':verified,'wrong_final':wrong,
         'copied_controls':controls,'control_receipt':receipt,
         'actual_author_unchanged':before['author']==after['author'],
         'actual_review_unchanged':before['review']==after['review'],
         'actual_context_unchanged':before['context']==after['context'],
         'external_context_count':len(contexts),'all_expected':ok}
    (parent/'contribution-r1-replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ['all_expected','source_records_strictly_authenticated','payload_files',
                                      'directories_including_packet_root','actual_author_unchanged',
                                      'actual_review_unchanged','actual_context_unchanged','external_context_count']}))
    print('Copied controls:',len(receipt['controls']))
    return 0 if ok else 1
if __name__=='__main__':sys.exit(main())
