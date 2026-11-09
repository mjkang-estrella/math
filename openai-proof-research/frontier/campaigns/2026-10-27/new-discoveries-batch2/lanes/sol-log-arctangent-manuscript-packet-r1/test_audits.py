import verify,os,json,shutil
P=verify.P;out=P/'initial-replay';pins=json.loads((P/'pins.json').read_text());env=dict(os.environ,LEAN_PATH=str(out)+':'+':'.join(d['path']+'/.lake/build/lib/lean' for d in pins['packages'].values()))
for p in sorted((P/'formal').glob('PacketAudit_*.lean')):
 shutil.copy2(p,out/p.name)
 r=verify.run([pins['lean_binary'],'-j1','-DwarningAsError=true','-DautoImplicit=false',p.name],out,out/'logs'/(p.stem+'.log'),env)
 print(p.stem,r,flush=True)
