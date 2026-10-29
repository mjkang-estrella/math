#!/usr/bin/env python3
"""Deterministic ZIP: sorted paths, fixed UTC metadata and permissions, no caches."""
from pathlib import Path
import hashlib,json,zipfile,sys
b=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def payload():
 files=[]
 for name in ['README.md','SUMMARY.md','PROOF.md','FORMAL-MAP.md','LIBRARY.md','ATTEMPTS.md','main.tex','paper.pdf','pins.json','component.json']:
  files.append(b/name)
 for name in ['formal','scripts','provenance','primary','verification/audit']:
  files.extend(p for p in (b/name).rglob('*') if p.is_file() and p.suffix not in {'.olean','.ilean','.ir','.o','.so','.pyc'} and '__pycache__' not in p.parts)
 files.extend(p for p in (b/'paper/build').iterdir() if p.is_file() and p.suffix in {'.log','.stdout','.stderr'})
 files.extend([b/'paper/qa.json',b/'paper/build-command.json'])
 files.extend(sorted((b/'paper/render').glob('final-*.png')))
 return sorted(set(files),key=lambda p:p.relative_to(b).as_posix())
def build(out):
 files=payload();manifest={p.relative_to(b).as_posix():sha(p) for p in files};data={str(p.relative_to(b)):p.read_bytes() for p in files};data['manifest.json']=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode()
 with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
  for n in sorted(data):
   i=zipfile.ZipInfo(n,date_time=(2026,10,28,0,0,0));i.create_system=3;i.external_attr=0o100644<<16;i.compress_type=zipfile.ZIP_DEFLATED;z.writestr(i,data[n],compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
 return {'sha256':sha(Path(out)),'payload_files_excluding_manifest':len(files),'payload_manifest':manifest}
if __name__=='__main__':
 out=Path(sys.argv[1]) if len(sys.argv)>1 else b/'packet/jacobi-shifted-source-proof.zip'
 result=build(out);print(json.dumps({k:v for k,v in result.items() if k!='payload_manifest'},indent=2))
