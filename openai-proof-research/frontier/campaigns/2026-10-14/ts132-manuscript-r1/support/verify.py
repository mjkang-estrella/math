#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang. No affiliation.
"""Read-only externally anchored manuscript identity/QA check. Not a proof oracle."""
import argparse, hashlib, json, pathlib, re, sys
ROOT=pathlib.Path(__file__).resolve().parents[1]

def need(c,m):
    if not c: raise ValueError(m)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def pairs(rows):
    out={}
    for k,v in rows:
        need(k not in out,'duplicate JSON key: '+k);out[k]=v
    return out
def read(p): return json.loads(p.read_text(),object_pairs_hook=pairs)
def safe(s):
    p=pathlib.PurePosixPath(s)
    need(isinstance(s,str) and s and not p.is_absolute() and '..' not in p.parts and str(p)==s and s!='.','unsafe/noncanonical path')
    return s

def inventory(root,manifest,anchor,replay=None):
    need(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'bad anchor syntax')
    need(not root.is_symlink() and not (root/manifest).is_symlink(),'linked root/manifest')
    need(sha(root/manifest)==anchor,'external anchor mismatch: '+str(root))
    obj=read(root/manifest);rows=obj['files'];need(isinstance(rows,list),'file inventory must be a list')
    names=[safe(x['path']) for x in rows];dirs=[safe(x) for x in obj['directories']]
    need(manifest not in names,'reserved manifest in payload')
    need(replay is None or replay=='.replays','unexpected unsealed area')
    if replay: need(all(n.split('/')[0]!=replay for n in names+dirs),'replay included in sealed inventory')
    need(len(names)==len(set(names)) and len(dirs)==len(set(dirs)),'duplicate inventory member')
    files=set();actualdirs=set()
    for p in root.rglob('*'):
        need(not p.is_symlink(),'linked member: '+str(p))
        rel=p.relative_to(root).as_posix()
        if replay and rel.split('/')[0]==replay: continue
        if p.is_file(): files.add(rel)
        elif p.is_dir(): actualdirs.add(rel)
        else: raise ValueError('special member: '+rel)
    need(files==set(names)|{manifest},'file membership mismatch: '+str(root))
    need(actualdirs==set(dirs),'directory membership mismatch: '+str(root))
    for row in rows:
        p=root/row['path']
        size=row.get('bytes',row.get('size'))
        need(p.stat().st_size==size and sha(p)==row['sha256'],'payload changed: '+str(p))
    return len(rows)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);ap.add_argument('--dependency-parent',type=pathlib.Path);args=ap.parse_args()
    parent=args.dependency_parent.resolve() if args.dependency_parent else ROOT.parent
    count=inventory(ROOT,'manifest.json',args.anchor)
    dependencies=read(ROOT/'inputs/dependencies.json')
    checked=[]
    for dep in dependencies:
        n=inventory(parent/safe(dep['directory']),dep['manifest'],dep['anchor'],dep.get('unsealed_replay_directory'))
        checked.append({'role':dep['role'],'payloads':n})
    repo=parent.parents[2]
    for row in read(ROOT/'inputs/explicit-inputs.json'):
        p=repo/safe(row['path'])
        need(p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],'input changed: '+str(p))
    author=parent/'fresh-structural-discovery-r27'
    tree=read(repo/'sources/preprints-tree.json');need(tree.get('truncated') is False,'incomplete source tree')
    blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    receipt=read(author/'source-receipt.json')
    need(receipt['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','wrong source pin')
    for row in receipt['files']:
        b=(author/row['local']).read_bytes()
        need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob']==blobs[row['path']],'source blob mismatch')
    build=read(ROOT/'checks/build-receipt.json');qa=read(ROOT/'checks/visual-review.json')
    need(sha(ROOT/'main.tex')==build['source_sha256'],'build/source mismatch')
    need(sha(ROOT/'formal-support.tex')==build['formal_support_sha256'],'build/formal prose mismatch')
    pdf=ROOT/'output/pdf/transitive-superquadratic-sensitivity.pdf'
    need(sha(pdf)==build['pdf_sha256']==qa['pdf_sha256'],'PDF/QA mismatch')
    need(build['pdf_pages']==build['rendered_pages']==len(qa['pages']),'page-count mismatch')
    need({row['page'] for row in qa['pages']}==set(range(1,build['pdf_pages']+1)),'page coverage mismatch')
    for row in qa['pages']:
        need(sha(ROOT/safe(row['file']))==row['sha256'],'page raster mismatch')
        need(row['visually_inspected'] is True,'page not inspected')
    for key in ['overfull_boxes','undefined','rerun','missing_glyphs']:
        need(build['log_findings'][key]==0,'unresolved build issue: '+key)
    print(json.dumps({'status':'IDENTITY_AND_QA_RECORDS_VERIFIED_NOT_MATHEMATICAL_VERDICT','payloads':count,'dependencies':checked,'source_blobs':len(receipt['files']),'pages':len(qa['pages'])},sort_keys=True))

def guard(event,args):
    if event=='open':
        mode=args[1];flags=args[2]
        if isinstance(mode,str) and any(c in mode for c in 'wax+'): raise PermissionError('writes forbidden')
        if isinstance(flags,int) and flags & (1|2|64|512|1024): raise PermissionError('write flags forbidden')
    if event.startswith(('subprocess.','socket.')) or event in {'os.system','os.remove','os.rename','os.mkdir','os.rmdir'}:
        raise PermissionError('side effect forbidden: '+event)
if __name__=='__main__':
    sys.addaudithook(guard)
    try:main()
    except Exception as e: print('VERIFICATION_FAILED: '+str(e),file=sys.stderr);sys.exit(1)
