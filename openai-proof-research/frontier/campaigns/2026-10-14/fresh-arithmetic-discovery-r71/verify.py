#!/usr/bin/env python3
"""Read-only, externally anchored artifact check; no proof verdict."""
import argparse, hashlib, json, os, re, stat, subprocess, sys
from pathlib import Path

def fail(message): raise RuntimeError(message)
def digest(data): return hashlib.sha256(data).hexdigest()
def safe_regular(path):
    s=path.lstat()
    if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1: fail('not a regular single-link file: '+str(path))
    return path.read_bytes()
def ancestors(path):
    for p in [path,*path.parents]:
        if p.is_symlink():fail('symlink ancestor: '+str(p))
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--expected-manifest-sha256',required=True);ap.add_argument('--root',type=Path,default=Path(__file__).absolute().parent);ap.add_argument('--check-private',action='store_true');a=ap.parse_args()
    if not re.fullmatch('[0-9a-f]{64}',a.expected_manifest_sha256):fail('external digest format')
    root=a.root.absolute();ancestors(root)
    raw=safe_regular(root/'MANIFEST.json')
    if digest(raw)!=a.expected_manifest_sha256:fail('external manifest digest mismatch')
    manifest=json.loads(raw);files=manifest['public_files']
    if not isinstance(files,dict) or any('/' in n or n in ('.','..','MANIFEST.json','MANIFEST.sha256','private') for n in files):fail('invalid flat manifest paths')
    actual=set()
    for p in root.iterdir():
        if p.name=='private':
            s=p.lstat()
            if not stat.S_ISDIR(s.st_mode):fail('private must be a real directory')
            continue
        safe_regular(p);actual.add(p.name)
    if actual!=set(files)|{'MANIFEST.json','MANIFEST.sha256'}:fail('public membership mismatch')
    if safe_regular(root/'MANIFEST.sha256').decode()!=a.expected_manifest_sha256+'  MANIFEST.json\n':fail('local convenience anchor mismatch')
    for name,expected in files.items():
        data=safe_regular(root/name)
        if digest(data)!=expected['sha256'] or len(data)!=expected['bytes']:fail('public file identity: '+name)
    receipts=json.loads(safe_regular(root/'source-receipts.json'))
    private_count=0
    if a.check_private:
        entries=[]
        for e in receipts['source_files']:entries.append((e['retained_path'],e['sha256'],e.get('git_blob')))
        for e in receipts['primary_files']:
            entries.extend([(e['path'],e['sha256'],None),(e['extracted_text_path'],e['extracted_text_sha256'],None)])
        for e in receipts['context_files']:entries.append((e['retained_path'],e['sha256'],None))
        for rel,sha,blob in entries:
            path=Path(rel)
            if path.is_absolute() or '..' in path.parts or not path.parts or path.parts[0]!='private':fail('private path escape')
            p=root/path;ancestors(p);data=safe_regular(p)
            if digest(data)!=sha:fail('private SHA256 mismatch: '+rel)
            if blob and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()!=blob:fail('private git blob mismatch: '+rel)
            private_count+=1
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
    result=subprocess.run([sys.executable,'-B',str(root/'check_exact.py')],capture_output=True,text=True,env=env,check=True)
    observed=json.loads(result.stdout);expected=json.loads(safe_regular(root/'exact-check-results.json'))
    if observed!=expected:fail('exact diagnostic output mismatch')
    print(json.dumps({'status':'PASS_INTEGRITY_AND_EXACT_DIAGNOSTICS_ONLY','public_payload_files':len(files),'private_files_checked':private_count,'full_target':'UNRESOLVED','count_change':0},sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as error:
        print(json.dumps({'status':'FAIL','reason':str(error)},sort_keys=True),file=sys.stderr);sys.exit(1)
