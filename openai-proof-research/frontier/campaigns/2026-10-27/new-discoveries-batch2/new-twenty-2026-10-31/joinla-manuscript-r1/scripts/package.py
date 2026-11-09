from pathlib import Path,PurePosixPath
import hashlib,json,zipfile,os
p=Path(__file__).resolve().parent.parent
h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
# The wrapper's receipt is emitted after this process returns, so it is outer-only.
outer={'full-dossier.zip','MANIFEST.sha256','ARCHIVES.sha256','receipts/dossier-zip.json','receipts/package-process.json'}
files=[f for f in sorted(p.rglob('*')) if f.is_file() and f.relative_to(p).parts[0] not in {'tmp','packet-test'} and str(f.relative_to(p)) not in outer]
manifest={str(f.relative_to(p)):h(f) for f in files}
(p/'MANIFEST.sha256').write_text(''.join(v+'  '+k+'\n' for k,v in manifest.items()))
archive=p/'full-dossier.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for f in files+[p/'MANIFEST.sha256']:z.write(f,str(f.relative_to(p)))
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None
 assert len(z.namelist())==len(set(z.namelist()))
 for n in z.namelist():
  name=PurePosixPath(n);assert not name.is_absolute() and '..' not in name.parts and '\\' not in n
  digest=hashlib.sha256(z.read(n)).hexdigest()
  assert digest==(h(p/n) if n=='MANIFEST.sha256' else manifest[n]),n
(p/'receipts/dossier-zip.json').write_text(json.dumps({'status':'PASS','archive_sha256':h(archive),'archive_bytes':archive.stat().st_size,'members':len(files)+1,'CRC':'PASS','all_member_hashes_match_manifest':True,'relative_safe_names':True,'packet_sha256':h(p/'source-only.zip'),'excluded':'tmp/, packet-test/, archive itself, MANIFEST.sha256 self-digest, ARCHIVES.sha256, outer archive-check and package-process receipts'},indent=2)+'\n')
(p/'ARCHIVES.sha256').write_text(''.join(h(p/n)+'  '+n+'\n' for n in ['full-dossier.zip','source-only.zip','MANIFEST.sha256','receipts/dossier-zip.json']))
print('Dossier sealed:',archive.stat().st_size,'bytes;',len(files)+1,'members')
print('SHA256',h(archive))
