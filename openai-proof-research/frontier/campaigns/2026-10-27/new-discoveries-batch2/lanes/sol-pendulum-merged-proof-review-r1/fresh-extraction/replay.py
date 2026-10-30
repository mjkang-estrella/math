import pathlib,json,sys,subprocess,zipfile,re,datetime
from audit_tools import sha,audit,dependencies,MODS
archive=pathlib.Path(sys.argv[1]).resolve();dest=pathlib.Path(sys.argv[2]).resolve()
assert not dest.exists()
with zipfile.ZipFile(archive) as z:
 assert all(not pathlib.Path(n).is_absolute() and '..' not in pathlib.Path(n).parts for n in z.namelist())
 assert not any(n.endswith(('.olean','.ilean','.ir','.o','.so','.olean.private','.olean.server')) for n in z.namelist())
 z.extractall(dest)
manifest=json.loads((dest/'manifest.json').read_text())
for f,h in manifest.items():assert sha(dest/f)==h,f
assert not list(dest.rglob('*.olean'))
r=subprocess.run([sys.executable,str(dest/'verify_inputs.py')],capture_output=True,text=True)
assert r.returncode==0,r.stderr
(dest/'pins-and-inputs.json').write_text(r.stdout)
for d in json.loads((dest/'dependency-hashes.json').read_text()):assert sha(pathlib.Path(d['path']))==d['sha256'],d['path']
(dest/'logs').mkdir()
steps=[]
for m in MODS+['FullAudit']:
 print('BUILD',m,flush=True)
 r=subprocess.run([sys.executable,str(dest/'guard.py'),m],capture_output=True,text=True)
 print(r.stdout,flush=True)
 assert r.returncode==0,r.stderr
 steps.append(json.loads((dest/'logs'/f'{m}.json').read_text()))
 if m!='FullAudit':assert (dest/'logs'/f'{m}.log').stat().st_size==0
rows=audit(dest)
assert rows==json.loads((dest/'actual-declarations.json').read_text())
assert dependencies(dest)==json.loads((dest/'dependency-hashes.json').read_text())
for f,h in manifest.items():assert sha(dest/f)==h,f
out={'actualUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'MANDATORY_MERGED_SOURCE_ONLY_REPLAY_PASS','source_claim_pass':True,'credit':0,'archive_sha256':sha(archive),'initial_own_prebuilt_artifacts':0,'declaration_count':len(rows),'steps':steps,'declarations':rows}
(dest/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
assert len(rows)==139
print('MANDATORY MERGED REPLAY PASS',len(rows),'declarations; unconditional SourceClaim')
