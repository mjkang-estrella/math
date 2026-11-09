#!/usr/bin/env python3
"""Read-only verification; explicit detached anchors are mandatory."""
import argparse,hashlib,json
from pathlib import Path,PurePosixPath

def sha(b):return hashlib.sha256(b).hexdigest()
def require(cond,msg):
    if not cond:raise ValueError(msg)
def verify(packet,report,final_sha,manifest_sha,report_sha):
    for label,h in [('FINAL',final_sha),('MANIFEST',manifest_sha),('REPORT',report_sha)]:
        require(len(h)==64 and all(c in '0123456789abcdef' for c in h),'invalid explicit '+label+' anchor')
    require(packet.is_dir(),'packet absent')
    require(not report.is_symlink(),'report symlink')
    require(not (packet/'FINAL.md').is_symlink(),'FINAL symlink')
    require(not (packet/'MANIFEST.json').is_symlink(),'manifest symlink')
    mb=(packet/'MANIFEST.json').read_bytes()
    require(sha(mb)==manifest_sha,'MANIFEST anchor mismatch')
    require(sha((packet/'FINAL.md').read_bytes())==final_sha,'FINAL anchor mismatch')
    require(sha(report.read_bytes())==report_sha,'REPORT anchor mismatch')
    m=json.loads(mb);require(m['schema']==1,'schema')
    expected={}
    for e in m['files']:
        name=e['path'];p=PurePosixPath(name)
        require(not p.is_absolute() and '..' not in p.parts and p.as_posix()==name,'unsafe member path')
        require(name!='MANIFEST.json' and name not in expected,'duplicate/self member')
        expected[name]=e
    require('FINAL.md' in expected,'FINAL absent from members')
    actual={}
    for p in packet.rglob('*'):
        require(not p.is_symlink(),'packet symlink')
        if p.is_file() and p.name!='MANIFEST.json':actual[p.relative_to(packet).as_posix()]=p
        elif p.is_file() and p!=packet/'MANIFEST.json':raise ValueError('nested manifest not admitted')
    require(set(actual)==set(expected),'member set mismatch')
    total=0
    for name,p in actual.items():
        b=p.read_bytes();e=expected[name]
        require(len(b)==e['bytes'] and sha(b)==e['sha256'],'member mismatch: '+name);total+=len(b)
    require(total==m['total_bytes'] and len(actual)==m['file_count'],'totals mismatch')
    return {'ok':True,'files':len(actual),'bytes':total,'read_only':True}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--packet',required=True);p.add_argument('--report',required=True)
    p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    try:print(json.dumps(verify(Path(a.packet),Path(a.report),a.final_sha256,a.manifest_sha256,a.report_sha256),sort_keys=True))
    except Exception as e:raise SystemExit('REJECT: '+str(e))
