import run_build as b
import pathlib,sys,subprocess,time,json
p=b.ROOT; name=sys.argv[1]; tag=sys.argv[2]; out=p/'build-01'; log=p/'iterations'/tag; log.mkdir(parents=True,exist_ok=False)
env={'PATH':str(b.LEAN.parent)+':/usr/bin:/bin','HOME':str(out),'LANG':'C.UTF-8','LEAN_NUM_THREADS':'1','LEAN_PATH':':'.join([str(out),*[str(q/'.lake/build/lib/lean') for q in sorted(b.PKG.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]])}
cmd=[str(b.LEAN),'-j1','-DwarningAsError=true','-o',str(out/'PolynomialConvexity'/f'{name}.olean'),f'PolynomialConvexity/{name}.lean']
start=time.time()
with (log/'stdout').open('wb') as a,(log/'stderr').open('wb') as c:
 try:r=subprocess.run(cmd,cwd=p/'src',env=env,stdout=a,stderr=c,preexec_fn=lambda:b.caps(12 if name=='Audit' else 8),timeout=240);code=r.returncode
 except subprocess.TimeoutExpired:code='wall_timeout'
(log/'receipt.json').write_text(json.dumps({'cmd':cmd,'exit':code,'seconds':time.time()-start,'AS_GiB':12 if name=='Audit' else 8,'CPU_s':180,'wall_s':240,'cpus':2}))
print((log/'stdout').read_text());print((log/'stderr').read_text());sys.exit(0 if code==0 else 1)
