from pathlib import Path
import hashlib,json,sys,zipfile,runpy
L=Path(__file__).parent.resolve()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def pairs():
 for r in json.loads((L/'freeze.json').read_text()):
  assert h(Path(r['copy']))==r['sha256']
  if r['scientific']:assert h(Path(r['original']))==r['sha256']
 for r in json.loads((L/'primary-freeze.json').read_text()):
  assert h(Path(r['original']))==h(L/r['copy'])==r['sha256']
 with zipfile.ZipFile(L/'source-only.zip') as z:
  for n in z.namelist():assert z.read(n)==(L/'extracted'/n).read_bytes(),n
 runpy.run_path(str(L/'extracted/verify_sources.py'),run_name='__main__')
 runpy.run_path(str(L/'extracted/verify_pins.py'),run_name='__main__')
if sys.argv[1]=='manifest':
 pairs()
 files={str(p.relative_to(L)):{'sha256':h(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
 (L/'manifest.json').write_text(json.dumps(files,indent=2)+'\n')
 print('manifest written',len(files))
else:
 assert sys.argv[1]=='verify'
 files=json.loads((L/'manifest.json').read_text())
 assert set(files)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
 for n,r in files.items():assert h(L/n)==r['sha256'] and (L/n).stat().st_size==r['bytes'],n
 pairs()
 r={'status':'PASS','verified_manifest_files':len(files),'manifest_sha256':h(L/'manifest.json'),'source_archive_sha256':h(L/'source-only.zip'),'scientific_originals_and_copies':'PASS','all_extracted_original_members':'byte identical','compiler_and_nine_pins':'PASS','administrative':'snapshot only','manifest_excludes':['manifest.json','verification-receipt.json'],'counts':'9/39/next40; unchanged by this lane'}
 (L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
