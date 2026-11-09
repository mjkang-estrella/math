import pathlib,os,subprocess,sys,zipfile,json
D=pathlib.Path(__file__).resolve().parents[1];fresh=D/'fresh-verified';fresh.mkdir(exist_ok=False)
with zipfile.ZipFile(D/'lean-packet.zip') as z:z.extractall(fresh)
S=fresh/'lean';root=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');paths=[p/'.lake/build/lib/lean' for p in root.iterdir() if (p/'.lake/build/lib/lean').exists()];env={**os.environ,'LEAN_PATH':':'.join(map(str,[S]+paths))};env["PATH"] = "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:"+os.environ["PATH"];binary=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
for mod in ['Separator','Certificate','Audit','AuditAll']:
 p=subprocess.run([str(binary/'lean'),'-M3500','-j2','-DwarningAsError=true','-o',mod+'.olean',mod+'.lean'],cwd=S,env=env)
 if p.returncode:sys.exit(p.returncode)
p=subprocess.run([str(binary/'leanchecker'),'-M3500','-j2','Certificate'],cwd=S,env=env)
if p.returncode:sys.exit(p.returncode)
print('FRESH STRICT REPLAY AND EXPLICIT MODULE LEANCHECKER PASSED')
