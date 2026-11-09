import os,pathlib,subprocess,json
D=pathlib.Path(__file__).resolve().parents[1]; P=D/'lean-packet'
root=pathlib.Path('/home/mj-kang/Documents/Dev/math'); bin=root/'dlp-research/.tools/lean-4.34.1-linux/bin'
pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
env={'LEAN_PATH':str(P)+':'+':'.join(str(p) for p in sorted(pkgs.glob('*/.lake/build/lib/lean'))),'PATH':str(bin)+':/usr/bin:/bin','LANG':'C.UTF-8','HOME':str(P)}
res={}
for f,expect in [('Controls.lean',0),('NegControl1.lean',1),('NegControl2.lean',1)]:
    r=subprocess.run([str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true',f],cwd=P,env=env,capture_output=True,text=True)
    ok=(r.returncode==0)==(expect==0); res[f]={'rc':r.returncode,'expected_success':expect==0,'as_expected':ok,'out':(r.stdout+r.stderr)[-600:]}
    print(f,'rc',r.returncode,'as expected' if ok else 'UNEXPECTED',flush=True)
(D/'outputs/lean-controls.json').write_text(json.dumps(res,indent=2)+'\n')
