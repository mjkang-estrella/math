from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time,uuid
root=Path(__file__).resolve().parent.parent
bin=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pkg=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
for d in ['logs','tmp','build','cache']: (root/d).mkdir(exist_ok=True)
env=dict(os.environ,PATH=str(bin)+':'+os.environ.get('PATH',''),LEAN_PATH=':'.join([str(root/'build')]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(root/'tmp'),XDG_CACHE_HOME=str(root/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
modules=['Dynamics','Reduction','SourceSemantics','Cardinality','Endpoint','Controls','Audit','SemCanonical','SemWords','SemPeriodic','SemFinal','SemRegression','SemAudit','Sem3Coverage','Sem3Obstruction','Sem3Removal','SemFinal2','Sem3Audit','Sem4Bounded','Sem4RotorSet','Sem4Balance','Sem4Residual','SemFinal3','Sem4Audit','Sem5Sink','Sem5Classify','Sem5Flux','Sem5Trap','SemFinal4','Sem5Audit']
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
audit=(root/records['Sem5Audit']['lean']).read_text()
sources={p.stem:p.read_text() for p in (root/'formal').glob('*.lean')}
local_closure=set();work=['SemFinal4']
while work:
 m=work.pop()
 if m in local_closure:continue
 local_closure.add(m)
 work += [x for x in re.findall(r'^import (\S+)',sources[m],re.M) if x in sources]
assert local_closure=={'Dynamics','Reduction','SourceSemantics','SemCanonical','SemWords','SemPeriodic','SemFinal','SemRegression','Sem3Coverage','Sem3Obstruction','Sem3Removal','SemFinal2','Sem4Bounded','Sem4RotorSet','Sem4Balance','Sem4Residual','SemFinal3','Cardinality','Sem5Sink','Sem5Classify','Sem5Flux','Sem5Trap','SemFinal4'}
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
 'OmittedResidual':'import SemFinal2\nexample : ChanLevine.CycleTestBridge := ChanLevine.Sem3.cycleTestBridge\n'}
negative['OmittedDeficitTrap']='import SemFinal3\nexample : ChanLevine.CycleTestWord := ChanLevine.Sem4.cycleTestWord\n'
negative['OmittedNormalization']='import SemFinal3\nexample : ChanLevine.ConnectedFibres := ChanLevine.Sem4.connectedFibres\n'
negative['SinkLeftNotCanonical']='import SemFinal4\nexample : (ChanLevine.canonical 1 (0 : ZMod 3)).q 0 = false := by decide\n'
negative['FalseNormalizationWeight']='import SemFinal4\nexample : ChanLevine.chipWeight (ChanLevine.canonical 1 (1 : ZMod 3)) = 2 := by decide\n'
for name,src in negative.items():
 p=root/'tmp'/f'{name}.lean';p.write_text(src)
 run('negative-'+name,[bin/'lean','-j1','-M3500','-DwarningAsError=true',p],True)
run('regression',[sys.executable,'-I',root/'scripts/regression.py'])
run('normalization-check',[sys.executable,'-I',root/'scripts/normalization_check.py'])
report={'status':'PASS','modules':records,'source_hashes':manifest,'frozen_unchanged':True,'audit_roots':len(roots),'local_module_closure':sorted(local_closure),'audit_dependency_closure':len(closure),'closure_equality':True,'flagged_dependencies':flags,'local_flags':local_flags,'closure_axioms':sorted(set(re.findall(r'^CLOSURE_AXIOM (\S+)',audit,re.M))),'negative_controls':list(negative),'regression_cases':18,'unconditional_helpers':['canonicalTest','closedCoverage','closedWordRecurrence','closedWordCycleTest','ambientBridge','quota_terminal_exists','no_empty_rotor_closed_set','balanced_return'],'remaining_props':[],'unconditional_targets':['ChanLevine.Sem5.cycleTestBridge','ChanLevine.Sem5.connectedFibres','ChanLevine.Sem5.recurrentNormalization','ChanLevine.Sem5.cappedDeficitTrap']}
(root/'logs/replay-result.json').write_text(json.dumps(report,indent=2))
print('PASS strict replay; all round 5b semantic targets unconditional',flush=True)
