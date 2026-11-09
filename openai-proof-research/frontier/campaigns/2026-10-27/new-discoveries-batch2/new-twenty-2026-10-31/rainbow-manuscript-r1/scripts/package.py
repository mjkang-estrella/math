from pathlib import Path
import json,hashlib,zipfile,datetime
P=Path(__file__).resolve().parents[1];B=P.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
originals={}
for name in ['input-before.json','root-input-before.json']:
 for r in json.loads((P/name).read_text()):
  assert sha(B/r['path'])==r['sha256']
  originals.setdefault(r['sha256'],[]).append(r['path'])
copyrows=[]
for folder in ['evidence','sources','safe-extraction']:
 for p in sorted((P/folder).rglob('*')):
  if p.is_file():copyrows.append({'path':str(p.relative_to(P)),'sha256':sha(p),'matches_frozen_paths':originals.get(sha(p),[])})
(P/'evidence-copy-manifest.json').write_text(json.dumps(copyrows,indent=2)+'\n')
source=[P/'manuscript.md',P/'scripts/render.py',P/'REPRODUCE.md']+sorted((P/'assets').rglob('*'))
source=[p for p in source if p.is_file()]
(P/'SOURCE-MANIFEST.sha256').write_text(''.join(sha(p)+'  '+str(p.relative_to(P))+'\n' for p in source))
exclude={'MANIFEST.sha256','archive-receipt.json','rainbow-dossier.zip','rainbow-paper-source.zip'}
payload=[p for p in sorted(P.rglob('*')) if p.is_file() and not any(q in {'.deps','tmp'} for q in p.relative_to(P).parts) and p.name not in exclude]
(P/'MANIFEST.sha256').write_text(''.join(sha(p)+'  '+str(p.relative_to(P))+'\n' for p in payload))
payload.append(P/'MANIFEST.sha256')
def archive(name,files):
 q=P/name
 with zipfile.ZipFile(q,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
  for p in files:z.write(p,str(p.relative_to(P)))
 with zipfile.ZipFile(q) as z:
  assert z.testzip() is None
  assert len(z.namelist())==len(set(z.namelist()))
  for n in z.namelist():
   assert not Path(n).is_absolute() and '..' not in Path(n).parts
   assert hashlib.sha256(z.read(n)).hexdigest()==sha(P/n)
 return {'path':name,'sha256':sha(q),'bytes':q.stat().st_size,'members':len(files),'crc_and_each_member_sha256':'PASS'}
receipts=[archive('rainbow-paper-source.zip',source+[P/'SOURCE-MANIFEST.sha256']),archive('rainbow-dossier.zip',payload)]
(P/'archive-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'archives':receipts,'full_zip_excludes':['.deps/ (expanded wheel installation)','tmp/ (temporary setup files)','ZIP files and external archive-receipt.json (no circular self-hash)'],'no_lean_executed':True},indent=2)+'\n')
print(json.dumps(receipts,indent=2))
