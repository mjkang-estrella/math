from pathlib import Path
import hashlib,json,zipfile,os
O=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(O/'raw/366974.jsonl')=='9b3dc9c18dde0785c0b01f868dfcea95d0780ae6f0536f087ee9ec9ca8bfa292'
assert '{{' not in (O/'paper-source.md').read_text()
assert json.loads((O/'inputs-before.json').read_text())==json.loads((O/'inputs-after.json').read_text())
# Final source integrity check immediately before packaging.
for k,v in json.loads((O/'inputs-before.json').read_text()).items():assert sha(O.parent/k)==v
excluded={'full-dossier.zip','manuscript.zip','SHA256SUMS','ARCHIVES.sha256','receipts/package-check.json','receipts/package-run.json'}
files=sorted(p for p in O.rglob('*') if p.is_file() and str(p.relative_to(O)) not in excluded and 'tmp' not in p.relative_to(O).parts)
manifest=''.join(sha(p)+'  '+p.relative_to(O).as_posix()+'\n' for p in files)
(O/'SHA256SUMS').write_text(manifest)
small=['paper.pdf','paper-source.md','paper.md','build_pdf.py','PROOF.md','REPRODUCE.md','results.json','SUMMARY.md','verify.py','cap.py']
with zipfile.ZipFile(O/'manuscript.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for n in small:z.write(O/n,n)
 # Needed to regenerate the manuscript's data tables.
 for n in ['evidence/discovery/outputs/pmd-certificate.json','receipts/arithmetic.json']:z.write(O/n,n)
with zipfile.ZipFile(O/'full-dossier.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in files+[O/'SHA256SUMS',O/'manuscript.zip']:z.write(p,p.relative_to(O).as_posix())
counts={}
for name in ['manuscript.zip','full-dossier.zip']:
 with zipfile.ZipFile(O/name) as z:
  assert z.testzip() is None
  for n in z.namelist():
   p=Path(n);assert not p.is_absolute() and '..' not in p.parts
   assert z.read(n)==(O/n).read_bytes(),n
  counts[name]=len(z.namelist())
(O/'ARCHIVES.sha256').write_text(''.join(sha(O/n)+'  '+n+'\n' for n in ['manuscript.zip','full-dossier.zip','lean-packet.tar.gz']))
(O/'receipts/package-check.json').write_text(json.dumps(dict(status='PASS',zip_member_counts=counts,manifest_payload_files=len(files),validation='All ZIP members decompressed, CRC checked, safe relative names, compared byte-for-byte with local payload; full frozen input hashes rechecked immediately before packaging',external_metadata=['ARCHIVES.sha256','receipts/package-check.json','receipts/package-run.json'],excluded='The full ZIP cannot contain itself. SHA256SUMS excludes generated ZIPs and the external archive/check receipts to avoid self-reference; full ZIP includes SHA256SUMS and manuscript.zip.',raw_line_hash=sha(O/'raw/366974.jsonl')),indent=2)+'\n')
print(json.dumps(counts));print('Archive CRCs, safe member paths, byte comparisons and final frozen hashes PASS.')
