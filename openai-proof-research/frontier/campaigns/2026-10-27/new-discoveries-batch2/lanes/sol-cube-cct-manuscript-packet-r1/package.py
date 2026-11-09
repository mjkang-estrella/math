from pathlib import Path
import hashlib,json,shutil,subprocess,sys,zipfile
L=Path(__file__).resolve().parent;P=L/'packet';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(L/'frozen/sol-cube-cct-source-formal-r1/source-only.tar.gz',P/'evidence/immutable-formal-source.tar.gz')
out=subprocess.run([sys.executable,str(P/'reproduce.py')],capture_output=True,text=True,check=True)
(P/'evidence/finite-reproduction.json').write_text(out.stdout)
shutil.copyfile(P/'actual-audit.json',P/'evidence/actual-audit.json')
originals=set(json.loads((P/'formal/source-manifest.json').read_text()))|{'source-manifest.json'}
files={}
for p in sorted(P.rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(P)
 if rel.parts[0]=='formal' and str(rel.relative_to('formal')) not in originals:continue
 if p.name=='package-files.json':continue
 assert p.suffix not in ['.olean','.ilean','.pyc']
 files[str(rel)]=sha(p)
(P/'package-files.json').write_text(json.dumps(files,indent=2,sort_keys=True)+'\n')
subprocess.run([sys.executable,str(P/'rebuild_zip.py'),str(L/'source-only.zip')],check=True)
with zipfile.ZipFile(L/'source-only.zip') as z:
 assert all(not n.startswith('/') and '..' not in Path(n).parts for n in z.namelist())
 z.extractall(L/'fresh-extraction')
subprocess.run([sys.executable,str(L/'fresh-extraction/rebuild_zip.py'),str(L/'rebuilt-source-only.zip')],check=True)
assert (L/'source-only.zip').read_bytes()==(L/'rebuilt-source-only.zip').read_bytes()
(L/'archive-rebuild.json').write_text(json.dumps({'status':'PASS','sha256':sha(L/'source-only.zip'),'members':len(files)+1,'fresh_extracted_rebuild_byte_identical':True,'own_compiled_artifacts':False,'PDF':'BLOCKED; no PDF authored; no PDF reproducibility claim'},indent=2)+'\n')
print('Package and extracted rebuild PASS')
