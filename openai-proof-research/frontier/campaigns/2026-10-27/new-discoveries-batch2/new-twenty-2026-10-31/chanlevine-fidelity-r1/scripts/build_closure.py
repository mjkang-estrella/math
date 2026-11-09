import hashlib,json,os,pathlib,re,subprocess,sys,time,uuid
lane=pathlib.Path(__file__).resolve().parent.parent
root=pathlib.Path(sys.argv[1]).resolve() if len(sys.argv)>1 else lane
binary=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pkg=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
for d in ['logs','tmp','build','cache']: (root/d).mkdir(exist_ok=True)
env=dict(os.environ,PATH=str(binary)+':'+os.environ['PATH'],LEAN_PATH=':'.join([str(root/'build')]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(root/'tmp'),XDG_CACHE_HOME=str(root/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
sources={p.stem:p for p in (root/'formal').glob('*.lean')}
order=[]
def visit(n):
 if n in order:return
 for d in re.findall(r'^import (\S+)',sources[n].read_text(),re.M):
  if d in sources:visit(d)
 order.append(n)
visit('ChanLevineFinal')
manifest={n:hashlib.sha256(sources[n].read_bytes()).hexdigest() for n in order}
fingerprint=hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest()
def run(label,args,fail=False):
 log=root/'logs'/f'{label}-{time.time_ns()}-{uuid.uuid4().hex[:6]}.log'
 with log.open('w') as f:
  p=subprocess.run(['/usr/bin/time','-v',sys.executable,'-I',str(lane/'build/scripts/cap.py')]+list(map(str,args)),cwd=root/'formal',env=env,stdout=f,stderr=subprocess.STDOUT)
 s=log.read_text()
 assert (p.returncode!=0 and 'error:' in s) if fail else (p.returncode==0 and 'error:' not in s),(label,str(log),s[-2000:])
 print(label,'PASS',flush=True)
 return str(log.relative_to(root))
records={}
for n in order:
 receipt=root/'build'/f'{n}.receipt.json'
 if receipt.exists() and json.loads(receipt.read_text()).get('fingerprint')==fingerprint:
  records[n]=json.loads(receipt.read_text());print(n,'RESUME',flush=True);continue
 a=run('lean-'+n,[binary/'lean','-j1','-M3500','-DwarningAsError=true','-o',root/'build'/f'{n}.olean',sources[n]])
 c=run('leanchecker-'+n,[binary/'leanchecker',n])
 records[n]={'fingerprint':fingerprint,'lean':a,'leanchecker':c}
 receipt.write_text(json.dumps(records[n],indent=2))
(root/'logs/build-result.json').write_text(json.dumps({'status':'PASS','order':order,'sources':manifest,'records':records},indent=2))
print('ALL PASS',len(order),flush=True)
