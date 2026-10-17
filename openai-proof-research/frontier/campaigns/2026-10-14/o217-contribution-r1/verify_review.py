#!/usr/bin/env python3
"""Offline read-only membership verifier for o217-contribution-r1. Original code Myeongjin Kang, MIT.
Checks bytes and membership only; not a mathematical or contribution verdict.
"""
import argparse,hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parent
AUTHOR=ROOT.parent/'fresh-analytic-discovery-r28'
PROJECT=ROOT.parents[3]

def sha(b):return hashlib.sha256(b).hexdigest()
def fail(m):raise ValueError(m)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);a=ap.parse_args()
    raw=(ROOT/'review-manifest.json').read_bytes()
    if sha(raw)!=a.anchor:fail('external review-manifest anchor mismatch')
    man=json.loads(raw)
    files={};dirs=[]
    for p in ROOT.rglob('*'):
        if p.is_symlink():fail('symlink disallowed: '+str(p))
        s=p.relative_to(ROOT).as_posix()
        if '__pycache__' in p.parts:fail('cache artifact present: '+s)
        if p.is_dir():dirs.append(s)
        elif s!='review-manifest.json':files[s]=sha(p.read_bytes())
    if sorted(dirs)!=man['directories']:fail('directory membership mismatch')
    if files!=man['files']:fail('file membership or digest mismatch')
    rec=json.loads((ROOT/'review-receipts.json').read_bytes())
    for name,d in rec['author_anchors'].items():
        if sha((AUTHOR/name).read_bytes())!=d:fail('author anchor mismatch: '+name)
    t=rec['complete_preprints_tree']
    tb=(PROJECT/t['path']).read_bytes()
    if sha(tb)!=t['sha256']:fail('complete preprints tree digest mismatch')
    tree=json.loads(tb)
    if tree.get('truncated',False) or len(tree['tree'])!=t['entries']:fail('incomplete preprint inventory')
    print(json.dumps({'status':'verified review membership and author anchors only','external_anchor':a.anchor,'files':len(files),'directories':len(dirs),'author_anchors':len(rec['author_anchors'])},indent=2))

if __name__=='__main__':
    try:main()
    except Exception as e:
        print('VERIFICATION FAILED: '+str(e),file=sys.stderr);sys.exit(1)
