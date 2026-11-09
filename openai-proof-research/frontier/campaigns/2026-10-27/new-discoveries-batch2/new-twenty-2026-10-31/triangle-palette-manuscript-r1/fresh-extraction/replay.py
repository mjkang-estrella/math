import os,pathlib,subprocess,resource,signal,time,json,hashlib
ROOT=pathlib.Path(__file__).resolve().parent
O=ROOT/'replay-receipts'; O.mkdir(exist_ok=True)
BIN=pathlib.Path(os.environ['LEAN_BIN']).resolve()
PACK=pathlib.Path(os.environ['LEAN_PACKAGES']).resolve()
F=ROOT/'proof'
env={'HOME':os.environ['HOME'],'PATH':str(BIN)+':/usr/bin:/bin','LANG':'C.UTF-8','LEAN_PATH':':'.join([str(F)]+[str(p/'.lake/build/lib/lean') for p in sorted(PACK.iterdir())]),'LEAN_NUM_THREADS':'1','MALLOC_ARENA_MAX':'2'}
cpus=sorted(os.sched_getaffinity(0))[:2]
def run(label,cmd):
 def setup():
  os.setsid(); os.sched_setaffinity(0,cpus); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
 start=time.monotonic();peak=0;why=None
 with (O/(label+'.log')).open('w') as f:
  p=subprocess.Popen(cmd,cwd=F,env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=setup)
  while p.poll() is None:
   rss=0
   for q in pathlib.Path('/proc').glob('[0-9]*'):
    try:
     s=(q/'stat').read_text().split()
     if int(s[4])==p.pid:rss+=int(s[23])*os.sysconf('SC_PAGE_SIZE')
    except (OSError,ValueError,IndexError):pass
   peak=max(peak,rss)
   if rss>6*1024**3 or time.monotonic()-start>140:
    why='RSS' if rss>6*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.05)
  p.wait()
 r={'label':label,'command':cmd,'cwd':str(F),'environment':env,'cpus':cpus,'cpu_limit':120,'wall_limit':140,'AS_GiB':64,'RSS_GiB':6,'sample_seconds':.05,'peak_rss_bytes':peak,'wall_seconds':time.monotonic()-start,'exit':p.returncode,'reason':why}
 (O/(label+'.receipt.json')).write_text(json.dumps(r,indent=2));print(label,p.returncode,round(r['wall_seconds'],2),peak,flush=True);return r

if __name__ == '__main__':
 pins=json.loads((ROOT/'pins.json').read_text())
 for n in ['lean','leanchecker']:
  assert hashlib.sha256((BIN/n).read_bytes()).hexdigest()==pins['binaries'][n]
 manifest=json.loads((ROOT/'source-manifest.json').read_text())
 for name,digest in manifest.items():
  assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest, name
 for n in ['Defs','BoolProbe','Checker','Endpoint']:
  assert not (F/(n+'.olean')).exists(), 'Use a fresh extraction'
  assert run('build-'+n,[str(BIN/'lean'),'-j1','-DwarningAsError=true','-o',n+'.olean',n+'.lean'])['exit']==0
 for n in ['Defs','BoolProbe','Checker','Endpoint']:
  assert run('kernel-'+n,[str(BIN/'leanchecker'),n])['exit']==0
 assert run('inventory',[str(BIN/'lean'),'-j1','-DwarningAsError=true','ReviewAudit.lean'])['exit']==0
 assert 'TOTAL 66' in (O/'inventory.log').read_text()
 assert run('sanity',[str(BIN/'lean'),'-j1','-DwarningAsError=true','ReviewSanity.lean'])['exit']==0
 (F/'FalseProof.lean').write_text('import Endpoint\nset_option warningAsError true\nexample : False := by exact True.intro\n')
 assert run('negative-false-proof',[str(BIN/'lean'),'-j1','-DwarningAsError=true','FalseProof.lean'])['exit']==1
 (F/'WrongEndpoint.lean').write_text('import Endpoint\nset_option warningAsError true\nexample : Palette.SourceClaim := Palette.source_refutation\n')
 assert run('negative-wrong-endpoint',[str(BIN/'lean'),'-j1','-DwarningAsError=true','WrongEndpoint.lean'])['exit']==1
 (F/'BadCertificate.olean').write_bytes(b'Deliberately invalid Lean certificate\n')
 assert run('negative-header',[str(BIN/'leanchecker'),'BadCertificate'])['exit']==1
 assert 'invalid header' in (O/'negative-header.log').read_text().lower()
 receipts=[json.loads(p.read_text()) for p in sorted(O.glob('*.receipt.json'))]
 assert all(r['reason'] is None for r in receipts)
 (O/'all-receipts.json').write_text(json.dumps(receipts,indent=2))
 (O/'result.json').write_text(json.dumps({'status':'PASS','builds':4,'leanchecker':4,'declarations':66,'negative_controls':3,'accepted_credit':0},indent=2))
