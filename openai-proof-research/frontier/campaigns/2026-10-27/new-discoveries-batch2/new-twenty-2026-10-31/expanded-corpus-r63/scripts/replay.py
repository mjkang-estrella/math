import os,pathlib,subprocess,json,hashlib,zipfile,shutil
D=pathlib.Path(__file__).resolve().parents[1];E=D/'fresh-extracted';P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');L='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/'
env=dict(os.environ,PATH=L+':'+os.environ.get('PATH',''),LEAN_PATH=':'.join([str(E)]+[str(p) for p in P.glob('*/.lake/build/lib/lean')]))
shutil.rmtree(E)
E.mkdir()
with zipfile.ZipFile(D/'proof-packet.zip') as z:
 for info in z.infolist():
  assert '/' not in info.filename and info.filename not in ['.','..']
  (E/info.filename).write_bytes(z.read(info))
steps=[('compile',[L+'lean','-j1','-DwarningAsError=true','-o','SignedMass.olean','SignedMass.lean']),('audit',[L+'lean','-j1','-DwarningAsError=true','Audit.lean']),('checker',[L+'leanchecker','SignedMass'])];res={}
for label,cmd in steps:
 p=subprocess.run(['timeout','140','python',str(D/'scripts/limited.py')]+cmd,cwd=E,env=env,capture_output=True,text=True)
 (D/f'outputs/fresh-{label}.log').write_text(p.stdout+p.stderr);res[label]={'exit':p.returncode,'command':cmd}
 if p.returncode:break
(D/'outputs/replay.json').write_text(json.dumps(res,indent=2)+'\n')
assert len(res)==3 and all(x['exit']==0 for x in res.values()),res
print(json.dumps(res))
