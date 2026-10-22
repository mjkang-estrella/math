#!/usr/bin/env python3
"""Read-only packet verification. All three detached anchors are mandatory."""
import argparse, hashlib, json, os, re, stat
from pathlib import Path

def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''): h.update(chunk)
    return h.hexdigest()

def inventory(root):
    files={}; dirs={'.':stat.S_IMODE(root.stat().st_mode)}
    assert not root.is_symlink(), 'symlink root'
    for dp,ds,fs in os.walk(root,followlinks=False):
        for name in ds+fs:
            p=Path(dp)/name
            assert not p.is_symlink(), 'symlink: '+str(p)
            rel=p.relative_to(root).as_posix()
            mode=stat.S_IMODE(p.stat().st_mode)
            if p.is_dir(): dirs[rel]=mode
            else:
                assert p.is_file(), 'nonregular file: '+rel
                files[rel]=(p.stat().st_size,mode,digest(p))
    return files,dirs

def verify(root,expected):
    for name,h in expected.items():
        assert re.fullmatch('[0-9a-f]{64}',h), 'invalid anchor'
        assert digest(root/name)==h, 'anchor mismatch: '+name
    assert json.loads((root/'ANCHORS.json').read_text())==expected, 'detached anchor record mismatch'
    m=json.loads((root/'MANIFEST.json').read_text())
    assert m['schema']=='arithmetic152-exact-packet-v1'
    wanted={}
    for x in m['files']:
        rel=x['path']; p=Path(rel)
        assert not p.is_absolute() and '..' not in p.parts and rel not in wanted, 'bad payload path'
        assert rel not in ('MANIFEST.json','REPORT.md','ANCHORS.json'), 'envelope in payload'
        wanted[rel]=(x['bytes'],x['mode'],x['sha256'])
    files,dirs=inventory(root)
    assert set(files)==set(wanted)|set(m['outside_manifest']), 'file inventory mismatch'
    assert dirs==m['directories'], 'directory inventory/mode mismatch'
    for rel,record in wanted.items(): assert files[rel]==record, 'payload mismatch: '+rel
    for rel,mode in m['outside_manifest'].items(): assert files[rel][1]==mode, 'envelope mode mismatch: '+rel
    assert wanted['FINAL.md'][2]==expected['FINAL.md'], 'FINAL manifest disagreement'
    binding=root/'private/source-bindings.json'
    if binding.exists():
        bs=json.loads(binding.read_text()); assert len(bs)==12
        for x in bs:
            p=root/x['local']; b=p.read_bytes()
            assert len(b)==x['size'] and hashlib.sha256(b).hexdigest()==x['sha256']
            assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']
        for x in json.loads((root/'private/include-closure.json').read_text()):
            assert (root/'private/source'/x['resolved']).is_file()
    return len(wanted)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,required=True)
    p.add_argument('--final-sha256',required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    expected={'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}
    try:
        before=inventory(a.root)
        n=verify(a.root,expected)
        assert inventory(a.root)==before, 'verification changed packet'
    except (AssertionError,OSError,ValueError,KeyError) as e:
        raise SystemExit('FAIL: '+str(e))
    print('OK: '+str(n)+' exact payloads; detached anchors; inventory/modes; read-only identity')
