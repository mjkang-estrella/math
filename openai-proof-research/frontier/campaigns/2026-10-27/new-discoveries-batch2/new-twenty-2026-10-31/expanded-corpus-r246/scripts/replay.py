import pathlib,subprocess,json,os,zipfile,hashlib,re,sys
D=pathlib.Path(__file__).resolve().parents[1]; B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
s=(D/'lean/Mobius.lean').read_text();assert not re.search(r'\b(sorry|admit|unsafe|native_decide|ofReduceBool|axiom)\b',s)
p=D/'proof-packet.zip'
with zipfile.ZipFile(p,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('Mobius.lean',s)
r=D/'replay/fresh';r.mkdir(exist_ok=False)
with zipfile.ZipFile(p) as z:
 assert z.namelist()==['Mobius.lean'];z.extractall(r)
env={**os.environ,'PATH':str(B)+':'+os.environ['PATH'],'LEAN_PATH':str(r),'LEAN_NUM_THREADS':'2'}
for name,cmd in [('fresh-build',[str(B/'lean'),'-j2','-M3500','-DwarningAsError=true','-o',str(r/'Mobius.olean'),str(r/'Mobius.lean')]),('fresh-checker',[str(B/'leanchecker'),'Mobius'])]:
 with (D/f'logs/{name}.log').open('w') as f:
  p=subprocess.run(cmd,env=env,cwd=r,stdout=f,stderr=subprocess.STDOUT,timeout=100)
 print(name,p.returncode,flush=True)
 if p.returncode:sys.exit(p.returncode)
(D/'replay/result.json').write_text(json.dumps({'status':'PASS','lean_version':'4.34.1','mathlib_used':False,'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'packet_sha256':hashlib.sha256((D/'proof-packet.zip').read_bytes()).hexdigest(),'trust_limits':'Prebuilt Init core dependencies trusted; no upstream source rebuild; checker from same installation. No independent source-fidelity/novelty review or root acceptance.'},indent=2))
