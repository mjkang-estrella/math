"""Deterministic final source-only archive; no compiler outputs or build directories."""
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,)*2)
import hashlib,json,signal,zipfile
from pathlib import Path
signal.alarm(230)
R=Path(__file__).resolve().parent
names=['paper.tex','paper.pdf','build_pdf.py','authoring-pins.json','package.py','reproduce.py','REPRODUCE.md','provenance.json','freeze-before.json','freeze-after.json','QA.json','IMPLEMENTATION.md']
files=[R/n for n in names]
for d in ['component','evidence','replay-evidence','qa']:
 files += [p for p in (R/d).rglob('*') if p.is_file()]
assert not any(p.suffix in ['.olean','.ilean','.ir','.o','.so','.pyc'] for p in files)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest={str(p.relative_to(R)):sha(p) for p in sorted(files)}
(R/'packet-manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
files.append(R/'packet-manifest.json')
with zipfile.ZipFile(R/'steiner-final-review-packet.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(files):
  info=zipfile.ZipInfo(str(p.relative_to(R)),date_time=(2026,10,29,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
  z.writestr(info,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
print('Final source-only archive',sha(R/'steiner-final-review-packet.zip'),len(files),'files')
