"""Read-only exact-set verification; detached anchors must be supplied explicitly."""
from pathlib import Path
import argparse, hashlib, json, sys

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    a=argparse.ArgumentParser()
    a.add_argument('--root',required=True)
    for name in ['final','manifest','report']:
        a.add_argument('--'+name+'-sha256',required=True)
    args=a.parse_args();r=Path(args.root)
    expected={'packet/FINAL.md':args.final_sha256,'MANIFEST.json':args.manifest_sha256,'REPORT.md':args.report_sha256}
    for p,h in expected.items():
        if len(h)!=64 or sha(r/p)!=h:
            raise ValueError('detached anchor mismatch: '+p)
    m=json.loads((r/'MANIFEST.json').read_text())
    if m['format']!='r160-exact-packet-v1':raise ValueError('manifest format')
    listed={x['path']:x for x in m['files']}
    if len(listed)!=len(m['files']):raise ValueError('duplicate manifest path')
    actual={}
    for p in (r/'packet').rglob('*'):
        if p.is_symlink():raise ValueError('symlink: '+str(p))
        if p.is_file():actual[p.relative_to(r).as_posix()]=p
    if set(actual)!=set(listed):raise ValueError('packet exact-set mismatch')
    total=0
    for s,p in actual.items():
        e=listed[s];b=p.read_bytes();total+=len(b)
        if len(b)!=e['bytes'] or hashlib.sha256(b).hexdigest()!=e['sha256']:
            raise ValueError('packet content mismatch: '+s)
        if (p.stat().st_mode & 0o777)!=e['mode']:raise ValueError('packet mode mismatch: '+s)
    if len(actual)!=m['file_count'] or total!=m['total_bytes']:raise ValueError('totals mismatch')
    print(json.dumps({'artifact_integrity_only':True,'exact_packet_files':len(actual),'packet_bytes':total,'detached_anchors_matched':True},sort_keys=True))

if __name__=='__main__':
    try:main()
    except Exception as e:
        print(str(e),file=sys.stderr);sys.exit(1)
