import pathlib,zipfile,stat,os,subprocess,json
D=pathlib.Path(__file__).resolve().parents[1];R=D/'extracted'
S=D.parent/'expanded-corpus-r108'/'350979-proof-source.zip'
with zipfile.ZipFile(S) as z:
 assert set(z.namelist())=={'Circulant.lean','Bridge.lean','Endpoint.lean','Audit.lean'}
 for x in z.infolist():
  assert not pathlib.PurePosixPath(x.filename).is_absolute() and '..' not in pathlib.PurePosixPath(x.filename).parts
  assert not stat.S_ISLNK(x.external_attr>>16) and x.file_size<1000000
  (R/x.filename).write_bytes(z.read(x))
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
os.environ['PATH']=str(B)+':'+os.environ['PATH']
os.environ['LEAN_PATH']=':'.join([str(R)]+[str(p/'.lake/build/lib/lean') for p in P.iterdir()]);os.environ['MALLOC_ARENA_MAX']='2'
steps=[]
for n in ['Circulant','Bridge','Endpoint','Audit']:
 cmd=[str(B/'lean'),'-j1','-DwarningAsError=true',str(R/(n+'.lean')),'-o',str(R/(n+'.olean'))]
 r=subprocess.run(['python3','-I',str(D/'scripts/limited.py'),n,*cmd],cwd=R)
 receipt=json.loads((D/'logs'/(n+'.receipt.json')).read_text());steps.append(receipt)
 if receipt['returncode']:break
else:
 os.environ['LEAN_NUM_THREADS']='1'
 for n in ['Circulant','Bridge','Endpoint','Audit']:
  subprocess.run(['python3','-I',str(D/'scripts/limited.py'),'checker-'+n,str(B/'leanchecker'),'-v',n],cwd=R)
(D/'replay.json').write_text(json.dumps(steps,indent=2))
