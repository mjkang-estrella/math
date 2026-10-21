"""Read-only byte/membership verifier. Requires three detached anchors; no math verdict."""
import argparse,hashlib,json,os,stat
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b): return hashlib.sha256(b).hexdigest()
def inventory(root):
    files={}; dirs=[]
    assert not root.is_symlink(), 'root symlink'
    for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
        for name in ds:
            p=Path(base)/name
            assert not p.is_symlink() and p.is_dir(), 'non-directory or symlink'
            dirs.append(str(p.relative_to(root)))
        for name in fs:
            p=Path(base)/name; s=p.lstat()
            assert stat.S_ISREG(s.st_mode) and s.st_nlink==1, 'nonregular or hardlinked file'
            rel=str(p.relative_to(root)); b=p.read_bytes()
            files[rel]={'size':len(b),'sha256':sha(b)}
    return files,sorted(dirs)
def verify(root,anchors):
    f,d=inventory(root)
    for name,h in anchors.items():
        assert len(h)==64 and all(c in '0123456789abcdef' for c in h), 'invalid detached anchor'
        assert name in f and f[name]['sha256']==h, 'detached anchor mismatch: '+name
    m=json.loads((root/'MANIFEST.json').read_text())
    assert m['schema']=='r114-exact-v1' and m['envelopes']==sorted(ENVELOPES), 'manifest schema'
    payload={k:v for k,v in f.items() if k not in ENVELOPES}
    assert payload==m['files'], 'payload bytes or file membership mismatch'
    assert d==m['directories'], 'directory membership mismatch'
    if m['kind']=='research':
        treebytes=(root/'packet/private/history/02-preprints-tree.json').read_bytes()
        assert sha(treebytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b', 'complete tree identity'
        tree=json.loads(treebytes)
        assert len(tree['tree'])==13223 and tree.get('truncated') is False, 'complete tree scope'
        entries={e['path']:e for e in tree['tree']}
        auth=json.loads((root/'packet/private/source/authentication.json').read_text())
        prefix='preprints/Integral-points-on-character-varieties-of-curves-September-25-2026/'
        expected={p for p,e in entries.items() if p.startswith(prefix) and e['type']=='blob' and p.endswith(('.md','.tex','.bib'))}
        assert {a['path'] for a in auth}==expected and len(auth)==13, 'canonical source selection'
        for a in auth:
            e=entries[a['path']]; b=(root/'packet/private/source'/a['local']).read_bytes()
            assert a['path']==prefix+a['local'], 'path binding'
            assert a['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+a['path'], 'pinned URL'
            assert len(b)==a['size']==e['size'] and sha(b)==a['sha256'], 'source size/sha'
            assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==a['git_blob']==e['sha'], 'source Git blob'
        # Selected-copy identity is separate from whole incoming-original certification.
        for a in json.loads((root/'packet/incoming-authentication.json').read_text()):
            b=(root/a['copy']).read_bytes()
            assert sha(b)==a.get('sha256',a.get('excerpt_sha256')), 'selected history-copy identity'
    else:
        assert m['kind']=='synthetic-control', 'unknown kind'
    return dict(status='PASS_ARTIFACT_ONLY',files=len(f),payload_files=len(payload),directories=len(d),kind=m['kind'],modes_checked=False)
def main():
    p=argparse.ArgumentParser(); p.add_argument('root',type=Path)
    for x in ('final','manifest','report'): p.add_argument('--'+x,required=True)
    a=p.parse_args(); anchors={'FINAL.md':a.final,'MANIFEST.json':a.manifest,'REPORT.md':a.report}
    try: print(json.dumps(verify(a.root,anchors),sort_keys=True))
    except (AssertionError,KeyError,ValueError,OSError) as e: print('FAIL: '+str(e));raise SystemExit(1)
if __name__=='__main__': main()
