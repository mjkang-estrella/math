import pathlib,os,subprocess,json,hashlib,zipfile,re,sys,shutil
D=pathlib.Path(__file__).resolve().parents[1];R=D/'replay'
if R.exists(): shutil.rmtree(R)
R.mkdir()
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
os.environ['PATH']=str(B)+':'+os.environ['PATH'];os.environ['LEAN_PATH']=':'.join([str(R)]+[str(p/'.lake/build/lib/lean') for p in P.iterdir()])
# Fresh source-only extraction. No local olean is shipped or reused.
with zipfile.ZipFile(D/'350979-proof-source.zip','w') as z:
 for name in ['Circulant.lean','Bridge.lean','Endpoint.lean','Audit.lean']:z.write(D/'lean'/name,name)
with zipfile.ZipFile(D/'350979-proof-source.zip') as z:z.extractall(R)
s='\n'.join((R/(n+'.lean')).read_text() for n in ['Circulant','Bridge','Endpoint']);assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',re.sub(r'/\-.*?\-/','',s,flags=re.S))
rec=[]
for name in ['Circulant','Bridge','Endpoint','Audit']:
 cmd=[str(B/'lean'),'-j1','-DwarningAsError=true',str(R/f'{name}.lean'),'-o',str(R/f'{name}.olean')]
 r=subprocess.run(cmd,cwd=R,capture_output=True,text=True);(R/f'{name}.log').write_text(r.stdout+r.stderr);rec.append({'command':cmd,'returncode':r.returncode});print(name,r.returncode,flush=True)
 if r.returncode:print(r.stdout+r.stderr);break
if all(r['returncode']==0 for r in rec):
 cmd=[str(B/'leanchecker'),'Circulant','Bridge','Endpoint','Audit'];r=subprocess.run(cmd,cwd=R,capture_output=True,text=True);(R/'leanchecker.log').write_text(r.stdout+r.stderr);rec.append({'command':cmd,'returncode':r.returncode});print('leanchecker',r.returncode,flush=True);print(r.stdout[-2000:]+r.stderr[-2000:])
(R/'replay.json').write_text(json.dumps({'steps':rec,'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'trust':'Prebuilt external mathlib oleans trusted; no full upstream rebuild or source-to-olean attestation'},indent=2)+'\n')
