import pathlib,json,hashlib,sys,zipfile,re,os,subprocess,resource,time,signal
D=pathlib.Path(__file__).resolve().parents[1]; A=D.parent/'expanded-corpus-r250'
H=lambda b:hashlib.sha256(b).hexdigest()
def dump(p,x): (D/p).write_text(json.dumps(x,indent=2)+'\n')
def freeze(tag):
 m=json.loads((D/'frozen-inputs.json').read_text()); bad=[p for p,h in m.items() if not pathlib.Path(p).is_file() or H(pathlib.Path(p).read_bytes())!=h];dump('receipts/frozen-'+tag+'.json',{'count':len(m),'mismatches':bad});assert not bad
BIN=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
PKG=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
order=['Bases',*[f'Cases{k}' for k in range(8)],'Endpoint','Final','Audit']
def run(name,args,expected=0):
 env={'HOME':os.environ['HOME'],'PATH':str(BIN)+':/usr/bin:/bin','LEAN_PATH':str(D/'fresh/build')+':'+':'.join(str(p) for p in sorted(PKG.glob('*/.lake/build/lib/lean'))),'MALLOC_ARENA_MAX':'2','OMP_NUM_THREADS':'2','OPENBLAS_NUM_THREADS':'1'}
 def pre():
  os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
 t=time.monotonic();peak=0;reason=None
 with (D/'logs'/f'{name}.log').open('w') as f:
  p=subprocess.Popen(args,cwd=D/'fresh',env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=pre)
  while p.poll() is None:
   try:peak=max(peak,int(next(l.split()[1] for l in pathlib.Path(f'/proc/{p.pid}/status').read_text().splitlines() if l.startswith('VmRSS:')))*1024)
   except (OSError,StopIteration):pass
   if peak>6*1024**3 or time.monotonic()-t>140:reason='RSS/wall';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.05)
  p.wait()
 rec={'command':args,'environment':env,'exit':p.returncode,'expected_exit':expected,'wall_s':time.monotonic()-t,'sampled_rss_bytes':peak,'reason':reason,'limits':{'cpu_s':120,'wall_s':140,'rss_bytes':6*1024**3,'as_bytes':12*1024**3,'cpus':2,'sampling_s':.05}}
 dump('receipts/'+name+'.json',rec);print(name,p.returncode,round(rec['wall_s'],2),flush=True);return p.returncode
if sys.argv[1]=='setup':
 freeze('before');(D/'fresh/src').mkdir(parents=True);(D/'fresh/build').mkdir()
 manifest=json.loads((A/'lean-source-manifest.json').read_text()); archive=A/'lean-packet-final.zip';assert H(archive.read_bytes())=='37ac427f63eb4b042682e321a024567564d6a502e37a32136c655e5b02a272fd'
 with zipfile.ZipFile(archive) as z:
  assert len(z.infolist())==len(manifest)==12;assert set(z.namelist())==set(manifest)
  for i in z.infolist():
   assert i.filename in ['src/'+n+'.lean' for n in order];assert not (i.external_attr>>16)&0o170000==0o120000
   b=z.read(i);assert H(b)==manifest[i.filename];assert b==(A/'lean'/pathlib.Path(i.filename).name).read_bytes();assert not re.search(rb'\b(sorry|admit|native_decide|ofReduceBool)\b|^\s*(axiom|unsafe|partial)\s',b,re.M);(D/'fresh'/i.filename).write_bytes(b)
 dump('receipts/zip.json',{'sha256':H(archive.read_bytes()),'members':manifest})
 dump('receipts/binaries.json',{str(p):H(p.read_bytes()) for p in [BIN/'lean',BIN/'leanchecker']})
 dump('receipts/dependencies.json',{str(p):H(p.read_bytes()) for p in PKG.glob('*/lake-manifest.json')})
elif sys.argv[1]=='replay':
 for n in order:
  assert run('lean-'+n,[str(BIN/'lean'),'-j1','-M3500','-DwarningAsError=true','-o',str(D/'fresh/build'/f'{n}.olean'),str(D/'fresh/src'/f'{n}.lean')])==0
  assert run('checker-'+n,[str(BIN/'leanchecker'),n])==0
 freeze('after-replay')
elif sys.argv[1]=='freeze':freeze(sys.argv[2])
