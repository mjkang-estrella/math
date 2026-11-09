from pathlib import Path
import json,zipfile,hashlib
L=Path(__file__).resolve().parents[1];P=L.parent
H=lambda b:hashlib.sha256(b).hexdigest()
def filehash(p):return H(p.read_bytes())
# Check frozen originals and the late parent receipts again immediately before sealing.
initial=json.loads((L/'receipts/inputs-before.json').read_text())
assert all(filehash(P/n)==v for n,v in initial.items())
parent=json.loads((L/'receipts/parent-final.json').read_text())
assert all(v['status']=='pending' or filehash(P/'submodsep-parent-final-r1'/n)==v['sha256_before'] for n,v in parent.items())
sources=['paper.ms','scripts/layout.tmac','scripts/build_pdf.py','REPRODUCE.md']
sm={n:filehash(L/n) for n in sources};(L/'paper-source.manifest.json').write_text(json.dumps(sm,indent=2)+'\n')
with zipfile.ZipFile(L/'paper-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for n in sources+['paper-source.manifest.json']:z.write(L/n,n)
# Superseded renderings remain in the lane but only approved-page images are authoritative.
excluded={'MANIFEST.sha256','DELIVERABLES.sha256','receipts/archive-verification.json','logs/package.log','logs/package.receipt.json'}
payload=[]
for p in sorted(L.rglob('*')):
 if not p.is_file():continue
 n=str(p.relative_to(L))
 if n in excluded or n in ['full-dossier.zip','paper-source.zip','lean-packet.zip'] or n.startswith('tmp/'):continue
 # Preserve all evidence ZIPs, and all frozen evidence. Outer packet remains included below.
 payload.append((n,filehash(p)))
payload.append(('lean-packet.zip',filehash(L/'lean-packet.zip')))
(L/'MANIFEST.sha256').write_text(''.join(h+'  '+n+'\n' for n,h in payload))
with zipfile.ZipFile(L/'full-dossier.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for n,h in payload:z.write(L/n,n)
 z.write(L/'MANIFEST.sha256','MANIFEST.sha256')
with zipfile.ZipFile(L/'full-dossier.zip') as z:
 assert z.testzip() is None
 assert len(z.namelist())==len(payload)+1
 assert all(H(z.read(n))==h for n,h in payload)
 assert z.read('MANIFEST.sha256')==(L/'MANIFEST.sha256').read_bytes()
with zipfile.ZipFile(L/'paper-source.zip') as z:
 assert z.testzip() is None
 assert all(H(z.read(n))==h for n,h in sm.items())
assert all(filehash(P/n)==v for n,v in initial.items())
receipt={'pass':True,'full_dossier_payload_files':len(payload),'full_zip_crc':'PASS','full_zip_internal_manifest':'PASS','source_zip':'PASS','frozen_inputs_unchanged':True,'parent_final_receipts_unchanged':True,'archives':{n:{'bytes':(L/n).stat().st_size,'sha256':filehash(L/n)} for n in ['full-dossier.zip','paper-source.zip','lean-packet.zip']}}
(L/'receipts/archive-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
outer=['full-dossier.zip','paper-source.zip','lean-packet.zip','MANIFEST.sha256','receipts/archive-verification.json']
(L/'DELIVERABLES.sha256').write_text(''.join(filehash(L/n)+'  '+n+'\n' for n in outer))
print(json.dumps(receipt,indent=2))
