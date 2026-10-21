#!/usr/bin/env python3
"""Read-only exact-packet verification; detached anchors are mandatory inputs."""
import argparse,hashlib,json,stat
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('root',type=Path)
for name in ('manifest','final','report'):p.add_argument('--'+name+'-sha256',required=True)
a=p.parse_args();root=a.root.resolve()
def fail(msg):raise SystemExit('FAIL: '+msg)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
for name,anchor in [('MANIFEST.json',a.manifest_sha256),('FINAL.md',a.final_sha256),('REPORT.md',a.report_sha256)]:
 f=root/name
 if not f.is_file() or f.is_symlink() or digest(f)!=anchor:fail('detached anchor '+name)
m=json.loads((root/'MANIFEST.json').read_text())
if m['format']!='r170-exact-packet-v1':fail('format')
exempt={'MANIFEST.json','FINAL.md','REPORT.md','ANCHORS.json'}
actual={};dirs={'.':stat.S_IMODE(root.stat().st_mode)}
for f in root.rglob('*'):
 rel=f.relative_to(root).as_posix()
 if f.is_symlink():fail('symlink '+rel)
 if f.is_dir():dirs[rel]=stat.S_IMODE(f.stat().st_mode)
 elif f.is_file() and rel not in exempt:actual[rel]=f
if set(actual)!=set(m['files']):fail('file census')
if dirs!=m['directories']:fail('directory census/modes')
for rel,f in actual.items():
 e=m['files'][rel];s=f.stat()
 if s.st_size!=e['bytes'] or stat.S_IMODE(s.st_mode)!=e['mode'] or digest(f)!=e['sha256']:fail('payload '+rel)
for rel in ['MANIFEST.json','FINAL.md','REPORT.md']:
 if stat.S_IMODE((root/rel).stat().st_mode)!=m['envelope_mode']:fail('envelope mode '+rel)
print('Artifact bytes verified:',len(actual),'files;',len(dirs),'directories. No mathematical gate.')
