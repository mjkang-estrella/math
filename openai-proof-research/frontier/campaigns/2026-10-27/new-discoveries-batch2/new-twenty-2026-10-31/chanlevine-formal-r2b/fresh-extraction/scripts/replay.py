from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time,uuid
root=Path(__file__).resolve().parent.parent
bin=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pkg=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
for d in ['logs','tmp','build','cache']: (root/d).mkdir(exist_ok=True)
env=dict(os.environ,PATH=str(bin)+':'+os.environ.get('PATH',''),LEAN_PATH=':'.join([str(root/'build')]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(root/'tmp'),XDG_CACHE_HOME=str(root/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
modules=['Dynamics','Reduction','SourceSemantics','Cardinality','Endpoint','Controls','Audit','SemCanonical','SemWords','SemPeriodic','SemFinal','SemRegression','SemAudit']
manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (root/'formal').glob('*.lean')}
frozen=json.loads((root/'frozen-before.json').read_text())
assert all(manifest[k]==v for k,v in frozen.items())
fingerprint=hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest()
def run(label,args,fail=False):
 log=root/'logs'/f'{label}-{time.time_ns()}-{uuid.uuid4().hex[:6]}.log'
 with log.open('w') as f:
  p=subprocess.run(['/usr/bin/time','-v',sys.executable,'-I',str(root/'scripts/cap.py')]+list(map(str,args)),cwd=root/'formal',env=env,stdout=f,stderr=subprocess.STDOUT)
 s=log.read_text()
 assert (p.returncode!=0 and 'error:' in s) if fail else (p.returncode==0 and 'error:' not in s),(label,str(log),s[-8000:])
 print(label,'PASS',log.name,flush=True)
 return str(log.relative_to(root))
records={}
for m in modules:
 receipt=root/'build'/f'{m}.receipt.json'
 if '--resume' in sys.argv and receipt.exists() and json.loads(receipt.read_text()).get('fingerprint')==fingerprint:
  records[m]=json.loads(receipt.read_text());print(m,'RESUME',flush=True);continue
 l=run('lean-'+m,[bin/'lean','-j1','-M3500','-DwarningAsError=true','-o',root/'build'/f'{m}.olean',m+'.lean'])
 c=run('leanchecker-'+m,[bin/'leanchecker',m])
 records[m]={'fingerprint':fingerprint,'lean':l,'leanchecker':c}
 receipt.write_text(json.dumps(records[m],indent=2))
audit=(root/records['SemAudit']['lean']).read_text()
roots=set(re.findall(r'^ROOT (\S+)',audit,re.M))
checks=dict((n,(u,p,i,e)) for n,u,p,i,e in re.findall(r'^CHECK (\S+) UNSAFE (\S+) PARTIAL (\S+) IMPLEMENTED_BY (.*?) EXTERN (\S+)',audit,re.M))
edges=re.findall(r'^EDGE (\S+) (\S+)',audit,re.M)
closure=set(roots)
while True:
 new=closure|{b for a,b in edges if a in closure}
 if new==closure:break
 closure=new
assert closure==set(checks)
assert len(closure)==int(re.search(r'TOTAL_CLOSURE (\d+)',audit)[1])
flags={n:row for n,row in checks.items() if row!=('false','false','none','false') or n.endswith('_unsafe_rec')}
local_flags={n:row for n,row in flags.items() if n in roots}
assert not local_flags
negative={
 'WrongCanonicalWeight':'import SemFinal\nexample : ChanLevine.chipWeight (ChanLevine.canonical 1 (1 : ZMod 3)) = 0 := by decide\n',
 'EmptyCycle':'import SemRegression\nexample : ChanLevine.CycleTest (ChanLevine.Config.mk (fun _ : ZMod 3 => 0) (fun _ => true)) := by unfold ChanLevine.CycleTest; decide\n',
 'WrongPeriodCoverage':'import SemFinal\nexample : (1 : ZMod 3) ∈ ([0,2] : List (ZMod 3)) := by decide\n',
 'OmittedResidual':'import SemFinal\nexample : ChanLevine.CycleTestBridge := ChanLevine.cycleTestBridge\n'}
for name,src in negative.items():
 p=root/'tmp'/f'{name}.lean';p.write_text(src)
 run('negative-'+name,[bin/'lean','-j1','-M3500','-DwarningAsError=true',p],True)
run('regression',[sys.executable,'-I',root/'scripts/regression.py'])
report={'status':'PASS','modules':records,'source_hashes':manifest,'frozen_unchanged':True,'audit_roots':len(roots),'audit_dependency_closure':len(closure),'closure_equality':True,'flagged_dependencies':flags,'local_flags':local_flags,'negative_controls':list(negative),'regression_cases':18,'unconditional_targets':['canonicalTest'],'remaining_props':['ClosedWordRecurrence','CycleTestWord','ClosedWordCycleTest','RecurrentNormalization','ClosedCoverage']}
(root/'logs/replay-result.json').write_text(json.dumps(report,indent=2))
print('PASS strict replay; conditional targets remain',flush=True)
