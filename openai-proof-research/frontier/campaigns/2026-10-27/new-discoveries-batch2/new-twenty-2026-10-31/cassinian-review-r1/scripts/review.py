from pathlib import Path
import hashlib,json,zipfile,subprocess,os,resource,time,datetime,urllib.request,sys
D=Path(__file__).resolve().parents[1]; S=D.parent/'expanded-corpus-r83'; root=Path('/home/mj-kang/Documents/Dev/math'); F=D/'extracted'; B=root/'dlp-research/.tools/lean-4.34.1-linux/bin'; P=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def manifest():return {str(p.relative_to(S)):sha(p) for p in sorted(S.rglob('*')) if p.is_file()}
def fetch(name,url):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalReview/1.0'}),timeout=40) as q:data=q.read();r.update(status=q.status,final_url=q.url)
  (D/'receipts'/name).write_bytes(data);r.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e:r['error']=str(e)
 (D/'receipts'/(name+'.receipt.json')).write_text(json.dumps(r,indent=2));print(r)
def limits():
 os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2])); resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
def run(name,args):
 env={'XDG_RUNTIME_DIR':'/run/user/1000','DBUS_SESSION_BUS_ADDRESS':'unix:path=/run/user/1000/bus','PATH':str(B)+':/usr/bin:/bin','LANG':'C.UTF-8','LEAN_PATH':str(F)+':'+':'.join(str(p) for p in sorted(P.glob('*/.lake/build/lib/lean'))),'LEAN_NUM_THREADS':'1','MALLOC_ARENA_MAX':'2'}
 t=time.monotonic()
 with (D/'logs'/(name+'.log')).open('w') as log:
  p=subprocess.Popen(["systemd-run","--user","--scope","--quiet","-p","MemoryMax=6G",*args],cwd=F,env=env,preexec_fn=limits,stdout=log,stderr=subprocess.STDOUT)
  try:rc=p.wait(timeout=140)
  except subprocess.TimeoutExpired:p.kill();p.wait();rc=-999
 r={'command':args,'rc':rc,'seconds':time.monotonic()-t,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'log_sha256':sha(D/'logs'/(name+'.log'))};(D/'logs'/(name+'.json')).write_text(json.dumps(r,indent=2));print(r)
if __name__=='__main__':
 action=sys.argv[1]
 if action=='bind':(D/'before.json').write_text(json.dumps(manifest(),indent=2))
 if action=='after':
  m=manifest();(D/'after.json').write_text(json.dumps(m,indent=2));print('unchanged',m==json.loads((D/'before.json').read_text()))
 if action=='extract':
  F.mkdir(exist_ok=True)
  with zipfile.ZipFile(S/'331705-proof-source.zip') as z:
   for i in z.infolist():
    p=Path(i.filename);assert not p.is_absolute() and '..' not in p.parts and not (i.external_attr>>16)&0o170000==0o120000;assert i.file_size<1000000
    assert p.suffix=='.lean';(F/p).write_bytes(z.read(i))
  print({p.name:sha(p) for p in F.iterdir()})
 if action=='build':run('build',[str(B/'lean'),'-j1','-DwarningAsError=true','-o','Cassinian.olean','Cassinian.lean'])
 if action=='checker':run('checker',[str(B/'leanchecker'),'Cassinian'])
 if action=='audit':run('audit',[str(B/'lean'),'-j1','-DwarningAsError=true','OwnAudit.lean'])
 if action=='fetch':fetch(sys.argv[2],sys.argv[3])
