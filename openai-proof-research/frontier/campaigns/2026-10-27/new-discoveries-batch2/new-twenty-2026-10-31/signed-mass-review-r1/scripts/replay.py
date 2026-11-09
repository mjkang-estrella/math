import pathlib,zipfile,os,subprocess,json
D=pathlib.Path(__file__).resolve().parents[1]; E=D/'extracted';E.mkdir(exist_ok=True)
Z=D.parent/'expanded-corpus-r63/proof-packet.zip'
with zipfile.ZipFile(Z) as z:
 for f in z.infolist():
  assert '/' not in f.filename and f.filename not in ['.','..']
  (E/f.filename).write_bytes(z.read(f))
L='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/'
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=dict(os.environ,PATH=L+':'+os.environ['PATH'],LEAN_PATH=':'.join([str(E.resolve())]+[str(p) for p in P.glob('*/.lake/build/lib/lean')]))
res={}
for name,cmd in [('build',[L+'lean','-j1','-DwarningAsError=true','-o','SignedMass.olean','SignedMass.lean']),('checker',[L+'leanchecker','SignedMass'])]:
 r=subprocess.run(['timeout','140','python',str(D/'scripts/limited.py')]+cmd,cwd=E,env=env,capture_output=True,text=True)
 (D/'logs'/ (name+'.log')).write_text(r.stdout+r.stderr);res[name]={'command':cmd,'exit':r.returncode}
(D/'receipts/replay.json').write_text(json.dumps(res,indent=2))
print(res)
