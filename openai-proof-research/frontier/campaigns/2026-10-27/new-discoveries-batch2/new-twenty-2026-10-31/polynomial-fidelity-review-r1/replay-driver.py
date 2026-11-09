import os,sys,pathlib,subprocess,resource,json,time,hashlib
ROOT=pathlib.Path(__file__).resolve().parent/'replay/extracted'
LEAN=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
PKG=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
def caps(gib=8):
    resource.setrlimit(resource.RLIMIT_AS,(gib*1024**3,gib*1024**3))
    resource.setrlimit(resource.RLIMIT_CPU,(180,180))
    os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
def build(src,out):
    out=pathlib.Path(out).resolve(); out.mkdir(parents=True,exist_ok=True)
    env={'MALLOC_ARENA_MAX':'2','PATH':str(LEAN.parent)+':/usr/bin:/bin','LANG':'C.UTF-8','LEAN_NUM_THREADS':'1',
         'LEAN_PATH':':'.join([str(out),*[str(p/'.lake/build/lib/lean') for p in sorted(PKG.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]])}
    pins=json.loads((ROOT/'pins.json').read_text())
    for binary,key in [(LEAN,'lean_binary_sha256'),(LEAN.parent/'leanchecker','leanchecker_sha256')]:
        if hashlib.sha256(binary.read_bytes()).hexdigest()!=pins[key]:
            raise RuntimeError('pinned binary hash mismatch: '+str(binary))
    results=[]
    for name in ['Source','Reindex','Convexity','Model','Tails','Moments','Integrability','Layercake','Factored','Boundaries','Gaps','Ties','Chambers','GapTransport','GapDomain','Identification','Endpoint','Audit']:
        file=src/'PolynomialConvexity'/f'{name}.lean'
        if not file.exists(): continue
        target=out/'PolynomialConvexity'/f'{name}.olean'; target.parent.mkdir(exist_ok=True)
        cmd=[str(LEAN),'-j1','-s8192','-DElab.async=false','-DwarningAsError=true','-o',str(target),str(file.relative_to(src))]
        gib=12 if name=='Audit' else 8
        start=time.time()
        with (out/f'{name}.stdout').open('wb') as a,(out/f'{name}.stderr').open('wb') as b:
            try: r=subprocess.run(cmd,cwd=src,env=env,stdout=a,stderr=b,preexec_fn=lambda: caps(gib),timeout=240); code=r.returncode
            except subprocess.TimeoutExpired: code='wall_timeout'
        results.append({'module':name,'command':cmd,'exit':code,'seconds':time.time()-start,'AS_GiB':gib,'CPU_s':180,'wall_s':240,'cpus':2})
        (out/'build.json').write_text(json.dumps(results,indent=2))
        print(name,code,flush=True)
        if code!=0:return False
    for name in ['Source','Reindex','Convexity','Model','Tails','Moments','Integrability','Layercake','Factored','Boundaries','Gaps','Ties','Chambers','GapTransport','GapDomain','Identification','Endpoint','Audit']:
        if not (src/'PolynomialConvexity'/f'{name}.lean').exists(): continue
        cmd=[str(LEAN.parent/'leanchecker'),'-v',f'PolynomialConvexity.{name}']
        start=time.time()
        with (out/f'{name}.checker.stdout').open('wb') as a,(out/f'{name}.checker.stderr').open('wb') as b:
            try: r=subprocess.run(cmd,cwd=src,env=env,stdout=a,stderr=b,preexec_fn=lambda: caps(12),timeout=240); code=r.returncode
            except subprocess.TimeoutExpired: code='wall_timeout'
        results.append({'checker':name,'command':cmd,'exit':code,'seconds':time.time()-start,'AS_GiB':12,'CPU_s':180,'wall_s':240,'cpus':2})
        (out/'build.json').write_text(json.dumps(results,indent=2))
        print('checker',name,code,flush=True)
        if code!=0:return False
    return True
if __name__=='__main__':sys.exit(0 if build(ROOT/'src',sys.argv[1]) else 1)
