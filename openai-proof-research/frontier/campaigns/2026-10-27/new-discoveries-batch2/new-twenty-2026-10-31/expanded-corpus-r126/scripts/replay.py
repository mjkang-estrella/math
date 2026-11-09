import pathlib,json,zipfile,hashlib,subprocess,os,sys
D=pathlib.Path(__file__).resolve().parents[1];F=D/'fresh-extraction';F.mkdir();zpath=D/'338258-proof-source.zip'
sha=lambda b:hashlib.sha256(b).hexdigest()
with zipfile.ZipFile(zpath) as z:
 for info in z.infolist():
  p=pathlib.Path(info.filename)
  assert not p.is_absolute() and '..' not in p.parts and len(p.parts)==1 and info.file_size<1000000 and p.suffix in ['.lean','.json','.md']
  assert (info.external_attr>>16)&0o170000 !=0o120000
  (F/p).write_bytes(z.read(info))
m=json.loads((F/'MANIFEST.json').read_text());assert set(m)=={p.name for p in F.iterdir() if p.name!='MANIFEST.json'}
for p,h in m.items():assert sha((F/p).read_bytes())==h
os.environ['LANE_BUILD']='fresh-extraction';mods=['Core']+[f'Row{i}' for i in range(15)]+['Table','Endpoint'];results=[]
def call(tag,args):
 subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),tag,sys.executable,'-I',str(D/'scripts/leanrun.py'),*args],check=True)
 r=json.loads((D/f'logs/{tag}.receipt.json').read_text());results.append({'tag':tag,**r});assert r['returncode']==0,(tag,r)
for mod in mods:call('fresh-'+mod,['-o',mod+'.olean',mod+'.lean'])
for mod in mods:call('check-'+mod,['--checker',mod])
call('fresh-audit',['-o','Audit.olean','Audit.lean'])
(D/'outputs/replay.json').write_text(json.dumps({'zip_sha256':sha(zpath.read_bytes()),'fresh_directory':str(F),'success':True,'results':results,'trust_limit':'Uses pinned cached mathlib oleans; no complete upstream rebuild claimed.'},indent=2)+'\n')
