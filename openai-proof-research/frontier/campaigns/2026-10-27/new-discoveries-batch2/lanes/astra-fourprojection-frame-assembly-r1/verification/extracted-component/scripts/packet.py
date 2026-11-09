"""Deterministic component packet, followed by fresh extracted strict replay."""
from pathlib import Path
import hashlib, io, json, shutil, subprocess, sys, zipfile
B=Path(__file__).resolve().parents[1]
files=sorted([*B.glob('formal/*.lean'), *B.glob('scripts/*.py'), *B.glob('source/*'), B/'SUMMARY.md', B/'provenance.json'],key=lambda p:str(p.relative_to(B)))
def packet_bytes():
    buf=io.BytesIO()
    with zipfile.ZipFile(buf,'w',compression=zipfile.ZIP_STORED) as z:
        for p in files:
            info=zipfile.ZipInfo(str(p.relative_to(B)),date_time=(1980,1,1,0,0,0))
            info.create_system=3
            info.external_attr=0o100644 << 16
            z.writestr(info,p.read_bytes())
    return buf.getvalue()
data=packet_bytes()
assert data==packet_bytes()
(B/'packet').mkdir(exist_ok=True)
archive=B/'packet'/'four-frame-component.zip'
archive.write_bytes(data)
dest=B/'verification'/'extracted-component'
if dest.exists():shutil.rmtree(dest)
dest.mkdir(parents=True)
with zipfile.ZipFile(archive) as z:z.extractall(dest)
for p in files:assert (dest/p.relative_to(B)).read_bytes()==p.read_bytes()
p=subprocess.run([sys.executable,str(dest/'scripts'/'replay.py')],cwd=dest,text=True,capture_output=True)
(B/'verification'/'extracted-replay.log').write_text(p.stdout+p.stderr)
print(p.stdout+p.stderr)
if p.returncode:raise SystemExit(p.returncode)
r=json.loads((dest/'verification'/'result.json').read_text())
original=json.loads((B/'verification'/'result.json').read_text())
for key in ['public_declaration_count','declarations','axioms','sources']:
    assert r[key]==original[key],key
out={'status':'PASS_EXTRACTED_COMPONENT_REPLAY','archive':str(archive.relative_to(B)),
 'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'deterministic_bytes_repeated':True,
 'extracted_sources_byte_identical':True,'strict_replay':r['status'],
 'declaration_count':r['public_declaration_count'],'axioms':r['axioms'],
 'source_conjecture_formalized':False}
(B/'verification'/'packet-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
