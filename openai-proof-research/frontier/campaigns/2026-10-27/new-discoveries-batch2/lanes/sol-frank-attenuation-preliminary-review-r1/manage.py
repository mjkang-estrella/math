import pathlib,json,hashlib,sys,shutil,datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
F=B/'lanes/root-frank-attenuation-preliminary-freeze-r1/review-freeze.json'
freeze=json.loads(F.read_text()); S=pathlib.Path(freeze['source'])
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
phase=sys.argv[1]
rows=[]
for f in freeze['files']:
 p=S/f['path']; row={'path':f['path'],'bytes':p.stat().st_size,'sha256':digest(p)}
 row['matches_freeze']=row['sha256']==f['sha256'] and row['bytes']==f['bytes']; rows.append(row)
 if phase=='before':
  dest=L/'inputs'/f['path'];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
assert all(x['matches_freeze'] for x in rows)
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'freeze_sha256':digest(F),'files':rows,'all_match':True}
(L/('input-'+phase+'.json')).write_text(json.dumps(out,indent=2)+'\n')
if phase=='before':
 shutil.copyfile(F,L/'review-freeze.json')
 shutil.copyfile(F.parent/'ASSESSMENT.md',L/'root-ASSESSMENT.md')
else:
 assert all(digest(L/'inputs'/r['path'])==r['sha256'] for r in rows)
 manifest=[{'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':digest(p)} for p in sorted(L.rglob('*')) if p.is_file() and p.name!='manifest.json']
 (L/'manifest.json').write_text(json.dumps({'files':manifest},indent=2)+'\n')
print(phase,len(rows),'matched')
