import run_build as b, sys, pathlib, subprocess, time, json
name=sys.argv[1]; tag=sys.argv[2]; out=b.ROOT/'work';out.mkdir(exist_ok=True);logs=b.ROOT/'iterations'/tag;logs.mkdir(parents=True,exist_ok=True)
env={'MALLOC_ARENA_MAX':'2','PATH':str(b.LEAN.parent)+':/usr/bin:/bin','LANG':'C.UTF-8','LEAN_NUM_THREADS':'1','LEAN_PATH':':'.join([str(out),*[str(p/'.lake/build/lib/lean') for p in sorted(b.PKG.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]])}
cmd=[str(b.LEAN),'--profile','-j1','-s8192','-DElab.async=false','-DwarningAsError=true','-o',str(out/'PolynomialConvexity'/f'{name}.olean'),f'PolynomialConvexity/{name}.lean'];start=time.time()
with (logs/'stdout').open('wb') as a,(logs/'stderr').open('wb') as c:
 try:r=subprocess.run(cmd,cwd=b.ROOT/'src',env=env,stdout=a,stderr=c,preexec_fn=lambda:b.caps(12 if name=='Audit' else 8),timeout=240);code=r.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
(logs/'receipt.json').write_text(json.dumps({'command':cmd,'exit':code,'seconds':time.time()-start,'AS_GiB':12 if name=='Audit' else 8,'CPU_s':180,'wall_s':240,'cpus':2,'threads':1},indent=2))
print((logs/'stdout').read_text());print((logs/'stderr').read_text());sys.exit(0 if code==0 else 1)
