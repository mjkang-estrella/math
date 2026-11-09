from pathlib import Path
import zipfile,hashlib,json
P=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
roots=['formal','inputs','supplement']
names=['main.tex','paper.pdf','README.md','PROOF.md','FAILURES.md','provenance.json','pins.json','input-before.json','input-after.json','verify.py','git_objects.py','build_pdf.py','pack.py','pdf-tools.json','pdf-reproduction.json']
for root in roots:names += [str(p.relative_to(P)) for p in (P/root).rglob('*') if p.is_file() and p.suffix not in ['.olean','.ilean','.pyc']]
names=sorted(names);assert all(not n.endswith(('.olean','.ilean','.pyc')) for n in names)
payload={n:(P/n).read_bytes() for n in names}
manifest=''.join(H(b)+'  '+n+'\n' for n,b in payload.items()).encode();payload['SHA256SUMS']=manifest
with zipfile.ZipFile(P/'packet.zip','w',compression=zipfile.ZIP_STORED) as z:
 for n in sorted(payload):
  i=zipfile.ZipInfo(n,(2026,10,29,0,0,0));i.create_system=3;i.external_attr=0o100644<<16;z.writestr(i,payload[n])
with zipfile.ZipFile(P/'packet.zip') as z:
 assert z.namelist()==sorted(payload)
 for line in z.read('SHA256SUMS').decode().splitlines():
  digest,n=line.split('  ',1);assert H(z.read(n))==digest
print(H((P/'packet.zip').read_bytes()))
