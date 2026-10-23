"""Read-only exact-packet verifier. Detached anchors must be supplied explicitly."""
from pathlib import Path
import argparse,hashlib,json,stat

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(packet,report,final_sha256,manifest_sha256,report_sha256):
    packet=Path(packet); report=Path(report)
    assert packet.resolve() not in report.resolve().parents,'REPORT must be outside packet'
    assert stat.S_IMODE(report.stat().st_mode)==0o444,'REPORT mode mismatch'
    assert digest(packet/'FINAL.md')==final_sha256,'FINAL anchor mismatch'
    assert digest(packet/'MANIFEST.json')==manifest_sha256,'MANIFEST anchor mismatch'
    assert digest(report)==report_sha256,'outside REPORT anchor mismatch'
    m=json.loads((packet/'MANIFEST.json').read_text())
    assert m['format']=='r204-exact-selection-v1','manifest format'
    expected={x['path'] for x in m['files']}; assert len(expected)==len(m['files']),'duplicate paths'
    assert 'MANIFEST.json' not in expected and 'FINAL.md' in expected,'invalid selection'
    actual_files=set();actual_dirs={'.'}
    for p in packet.rglob('*'):
        assert not p.is_symlink(),'symlink forbidden'
        rel=p.relative_to(packet).as_posix()
        if p.is_dir():actual_dirs.add(rel)
        elif p.is_file():actual_files.add(rel)
        else:raise AssertionError('unexpected node type')
    assert actual_files==expected|{'MANIFEST.json'},'exact file selection mismatch'
    assert actual_dirs==set(m['directories']),'exact directory selection mismatch'
    for rel,mode in m['directories'].items():
        assert stat.S_IMODE((packet/rel).stat().st_mode)==int(mode,8),'directory mode mismatch: '+rel
    assert stat.S_IMODE((packet/'MANIFEST.json').stat().st_mode)==int(m['manifest_mode'],8),'manifest mode'
    for x in m['files']:
        rel=x['path'];assert rel and not rel.startswith('/') and '..' not in Path(rel).parts,'unsafe path'
        p=packet/rel
        assert p.stat().st_size==x['bytes'],'size mismatch: '+rel
        assert stat.S_IMODE(p.stat().st_mode)==int(x['mode'],8),'file mode mismatch: '+rel
        assert digest(p)==x['sha256'],'digest mismatch: '+rel
    return {'verified_files':len(expected),'verified_directories':len(actual_dirs),'explicit_anchors':3,'writes':0}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--packet',required=True);p.add_argument('--report',required=True)
    for n in ['final','manifest','report']:p.add_argument('--'+n+'-sha256',required=True)
    a=p.parse_args();print(json.dumps(verify(a.packet,a.report,a.final_sha256,a.manifest_sha256,a.report_sha256)))
