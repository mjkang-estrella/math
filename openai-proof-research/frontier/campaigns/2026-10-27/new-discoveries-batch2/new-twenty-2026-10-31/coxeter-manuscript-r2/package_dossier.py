from pathlib import Path,PurePosixPath
import hashlib,json,zipfile,datetime,stat,subprocess,os
w=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
excluded={'tools','tmp','cache','dossier-check'}
skip={'dossier-manifest.json','dossier.zip','archive-receipt.json','package-check.json','process-check.json'}
files=[]
for p in w.rglob('*'):
 r=p.relative_to(w)
 if not p.is_file() or any(x in excluded for x in r.parts) or p.name in skip:continue
 if r.parts[0]=='receipts' and p.name in ['package.json','verify-extracted.json','final-handback.json']:continue
 if p.suffix in ['.olean','.ilean']:continue
 files.append(p)
m={'scope':'AI-assisted DRAFT, credit 0; source hold resolved as qualified limitation; root final receipts pending at cutoff','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':{str(p.relative_to(w)):h(p) for p in sorted(files)}}
(w/'dossier-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
with zipfile.ZipFile(w/'dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files)+[w/'dossier-manifest.json']:z.write(p,p.relative_to(w))
r={'file':'dossier.zip','sha256':h(w/'dossier.zip'),'bytes':(w/'dossier.zip').stat().st_size,'entries':len(files)+1,'manifest_sha256':h(w/'dossier-manifest.json')}
(w/'archive-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
d=w/'dossier-check';assert not d.exists();d.mkdir()
with zipfile.ZipFile(w/'dossier.zip') as z:
 for i in z.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
  q=d/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(z.read(i))
 for name,hsh in m['files'].items():assert h(d/name)==hsh,name
subprocess.run(['python3','-I',str(d/'verify_dossier.py')],check=True)
(w/'package-check.json').write_text(json.dumps({'safe_full_dossier_extraction':'PASS','all_packaged_hashes':'PASS','verifier':'PASS','current_packet_sha256':h(d/'frozen/330264-replay-fit-r2-source.zip'),'archive_sha256':r['sha256'],'Lean_run':False,'entries':r['entries']},indent=2)+'\n')
print(r)
