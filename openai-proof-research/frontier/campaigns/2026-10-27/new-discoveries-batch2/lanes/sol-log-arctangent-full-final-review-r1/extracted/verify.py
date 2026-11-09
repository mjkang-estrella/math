#!/usr/bin/env python3
"""Serial isolated replay; no original output oleans are in LEAN_PATH."""
import os,sys,json,hashlib,subprocess,time,signal,shutil,struct
from pathlib import Path
from git_objects import Objects
P=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def assert_pins():
 pins=json.loads((P/'pins.json').read_text()); binary=Path(pins['lean_binary'])
 assert H(binary)==pins['lean_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
 assert subprocess.check_output([str(binary),'--version'],text=True).strip()==pins['lean_version']
 for name,d in pins['packages'].items():
  p=Path(d['path']); g=p/'.git'; assert g.is_dir()
  ref=(g/'HEAD').read_text().strip()
  if ref.startswith('ref: '):
   r=ref[5:]; f=g/r
   ref=f.read_text().strip() if f.exists() else dict(line.split()[::-1] for line in (g/'packed-refs').read_text().splitlines() if line and not line.startswith(('#','^')))[r]
  assert ref==d['revision'],name
  # Compare every index entry's actual blob hash: detects tracked changes without git commands.
  tree=Objects(g).tree(ref)
  indexed={}
  data=(g/'index').read_bytes();magic,version,n=struct.unpack('!4sII',data[:12]);assert magic==b'DIRC' and version in (2,3)
  off=12
  for _ in range(n):
   start=off;mode=struct.unpack('!I',data[off+24:off+28])[0];oid=data[off+40:off+60].hex();flags=struct.unpack('!H',data[off+60:off+62])[0];off+=62
   if version==3 and flags&0x4000:off+=2
   end=data.index(b'\0',off);path=data[off:end].decode();off=start+((end+1-start+7)//8)*8
   f=p/path
   if mode!=0o160000:indexed[path]=oid
   if mode==0o160000:continue
   b=os.readlink(f).encode() if f.is_symlink() else f.read_bytes()
   assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==oid,(name,path)
  assert tree==indexed,('index differs from pinned commit',name)
 return pins

def run(cmd,cwd,log,env,wall=240):
 p=subprocess.Popen(cmd,cwd=cwd,stdout=log.open('wb'),stderr=subprocess.STDOUT,env=env,start_new_session=True)
 start=time.monotonic();peak=0;reason=None
 while p.poll() is None:
  rss=0
  for entry in Path('/proc').iterdir():
   if not entry.name.isdigit():continue
   try:
    st=(entry/'stat').read_text().rsplit(')',1)[1].split()
    if int(st[2])==p.pid:rss+=int(st[21])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,ValueError,IndexError):pass
  peak=max(peak,rss)
  if rss>=3*1024**3 or time.monotonic()-start>wall:
   reason='RSS limit' if rss>=3*1024**3 else 'wall deadline';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.04)
 rc=p.wait();record={'command':cmd,'exit':rc,'peak_group_sampled_RSS_bytes':peak,'wall_seconds':time.monotonic()-start,'failure':reason}
 assert rc==0 and reason is None,(record,str(log))
 return record

def verify_manifest():
 manifest=P/'SHA256SUMS'
 if manifest.exists():
  for line in manifest.read_text().splitlines():
   digest,name=line.split('  ',1);assert H(P/name)==digest,('payload changed',name)

def main():
 out=P/(sys.argv[1] if len(sys.argv)>1 else 'replay');out.mkdir(exist_ok=False);(out/'logs').mkdir()
 verify_manifest()
 pins=assert_pins();dump(out/'pins-before.json',pins)
 frozen=json.loads((P/'inputs/integrated-core-hashes.json').read_text())
 files={n:P/'formal'/f'{n}.lean' for n in frozen['mathematical_modules']}
 for n,p in files.items():assert H(p)==frozen['sha256']['formal/'+p.name]
 audits=sorted((P/'formal').glob('PacketAudit_*.lean'))
 for p in audits:files[p.stem]=p
 seen=set();order=[]
 def visit(n):
  if n in seen:return
  seen.add(n)
  for line in files[n].read_text().splitlines():
   if line.startswith('import '):
    for dep in line.split()[1:]:
     if dep in files:visit(dep)
  order.append(n)
 for n in sorted(files):visit(n)
 for n,p in files.items():shutil.copy2(p,out/p.name)
 env=dict(os.environ);env['LEAN_PATH']=str(out)+':'+':'.join(d['path']+'/.lake/build/lib/lean' for d in pins['packages'].values())
 for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:env[k]='1'
 records=[]
 for n in order:
  r=run([pins['lean_binary'],'-j1','-DwarningAsError=true','-DautoImplicit=false','-o',n+'.olean',n+'.lean'],out,out/'logs'/f'{n}.log',env)
  records.append(r);dump(out/'replay.json',records);print(n,'PASS',r['peak_group_sampled_RSS_bytes'],flush=True)
 audit='\n'.join((out/'logs'/(p.stem+'.log')).read_text() for p in audits);assert 'AUDIT_TOTAL' in audit and 'unsafe=true' not in audit
 # Every consumed module resolves to source, with exact hashes (including upstream Lean sources).
 roots=[Path(d['path']) for d in pins['packages'].values()]+[Path(pins['lean_binary']).parents[1]/'src/lean']
 consumed={}
 for mod in sorted(set(mod for f in out.glob('dependencies_*.txt') for mod in f.read_text().splitlines())):
  rel=mod.replace('.','/')+'.lean'; candidates=[out/rel]+[r/rel for r in roots]
  src=next((x for x in candidates if x.is_file()),None)
  assert src is not None,('missing consumed source',mod)
  consumed[mod]={'path':str(src),'sha256':H(src)}
 dump(out/'consumed-source-hashes.json',consumed)
 verify_manifest()
 assert_pins();assert all(H(p)==frozen['sha256']['formal/'+p.name] for n,p in files.items() if not n.startswith('PacketAudit_'))
 subprocess.run([sys.executable,str(P/'supplement/exact_check.py')],check=True,env=env,timeout=45)
 dump(out/'RESULT.json',{'status':'PASS','modules':len(order),'consumed_sources':len(consumed),'audit_total':sum(int(line.split('AUDIT_TOTAL ')[1]) for line in audit.splitlines() if 'AUDIT_TOTAL ' in line),'credit':0})
if __name__=='__main__':main()
