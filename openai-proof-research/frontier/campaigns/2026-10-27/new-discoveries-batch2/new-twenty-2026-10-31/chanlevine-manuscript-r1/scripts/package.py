from pathlib import Path,PurePosixPath
import hashlib,json,zipfile
p=Path.cwd();h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
exclude={'chanlevine-full-dossier.zip','DOSSIER-MANIFEST.json','DELIVERY-SHA256.json','package-validation.json'}
files=sorted(f for f in p.rglob('*') if f.is_file() and f.name not in exclude and '__pycache__' not in f.parts)
manifest={str(f.relative_to(p)):{'sha256':h(f),'bytes':f.stat().st_size} for f in files}
(p/'DOSSIER-MANIFEST.json').write_text(json.dumps({'algorithm':'sha256','exclusions':sorted(exclude),'files':manifest},indent=2)+'\n')
files.append(p/'DOSSIER-MANIFEST.json')
with zipfile.ZipFile(p/'chanlevine-full-dossier.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for f in files:z.write(f,str(f.relative_to(p)))
with zipfile.ZipFile(p/'chanlevine-full-dossier.zip') as z:
 assert z.testzip() is None
 assert len(z.namelist())==len(set(z.namelist()))
 for f in files:
  name=str(f.relative_to(p));q=PurePosixPath(name);assert not q.is_absolute() and '..' not in q.parts
  assert hashlib.sha256(z.read(name)).hexdigest()==h(f)
(p/'package-validation.json').write_text(json.dumps({'all_members_hash_verified':True,'crc_test_passed':True,'safe_names':True,'members':len(files),'self_reference_excluded':True},indent=2)+'\n')
(p/'DELIVERY-SHA256.json').write_text(json.dumps({f.name:h(f) for f in [p/'paper.pdf',p/'paper.md',p/'chanlevine-assembly-source.zip',p/'chanlevine-full-dossier.zip',p/'DOSSIER-MANIFEST.json',p/'package-validation.json']},indent=2)+'\n')
print('Packaged and verified',len(files),'members')
