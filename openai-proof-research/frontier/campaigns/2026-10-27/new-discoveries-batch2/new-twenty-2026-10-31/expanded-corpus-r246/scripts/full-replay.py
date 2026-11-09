import pathlib,zipfile,os,subprocess,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];p=D/'proof-packet-full.zip';r=D/'replay/full-fresh';r.mkdir();b='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'
with zipfile.ZipFile(p) as z:
 assert sorted(z.namelist())==['Audit.lean','Mobius.lean','README.md'];z.extractall(r)
env={**os.environ,'PATH':b+':'+os.environ['PATH'],'LEAN_PATH':str(r),'LEAN_NUM_THREADS':'2'}
steps=[('build',[b+'/lean','-j2','-M3500','-DwarningAsError=true','-o','Mobius.olean','Mobius.lean']),('checker',[b+'/leanchecker','Mobius']),('audit',[b+'/lean','-j2','-M3500','-DwarningAsError=true','Audit.lean'])];out={}
for name,cmd in steps:
 with (D/f'logs/full-{name}.log').open('w') as f:p1=subprocess.run(cmd,cwd=r,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=80)
 out[name]=p1.returncode;assert p1.returncode==0,out
out.update(status='PASS',packet_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audited_declarations=19,lean='4.34.1',mathlib=False,trust='Prebuilt core oleans trusted; same-installation kernel checker; no source rebuild of upstream.')
(D/'replay/full-result.json').write_text(json.dumps(out,indent=2));print(out)
