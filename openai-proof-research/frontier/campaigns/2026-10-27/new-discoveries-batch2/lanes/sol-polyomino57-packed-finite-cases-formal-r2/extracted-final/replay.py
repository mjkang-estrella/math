from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time,resource,signal,shlex
resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((L/'pins.json').read_text())
assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
assert subprocess.check_output([pins['lean_binary'],'-j1','--version'],text=True).strip()==pins['lean_version']
# Launch-only shell broker preserves the monitored Lean process's separate RSS policy.
# All Python orchestration and data processing then use a hard 512MiB AS limit.
broker=subprocess.Popen(['/bin/bash'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
def rev(repo):
 g=repo/'.git'
 if g.is_file():g=(repo/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(g/'HEAD').read_text().strip()
 if not head.startswith('ref: '):return head
 ref=head[5:]
 if (g/ref).exists():return (g/ref).read_text().strip()
 for line in (g/'packed-refs').read_text().splitlines():
  if line.endswith(' '+ref):return line.split()[0]
 raise AssertionError(str(repo))
for pkg in pins['packages'].values():assert rev(Path(pkg['path']))==pkg['revision']
for f,v in json.loads((L/'source-manifest.json').read_text()).items():
 p=L/f;assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes'],f
(L/'runs.jsonl').rename(L/'development-runs.jsonl')
work=L/'fresh-build';assert not work.exists();work.mkdir()
logs=L/'verification';logs.mkdir()
mods=json.loads((L/'modules.json').read_text())
for m in mods+['FiniteAudit']:
 p=L/'formal'/(m+'.lean');(work/p.name).write_bytes(p.read_bytes())
 if m!='FiniteAudit':assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',p.read_text())
t=time.monotonic()
def run(m):
 logfile=logs/(m+'.log')
 command=' '.join(shlex.quote(x) for x in [sys.executable,str(L/'run.py'),'-o',m+'.olean',m+'.lean'])
 broker.stdin.write('cd '+shlex.quote(str(work))+'\n'+command+' > '+shlex.quote(str(logfile))+' 2>&1\nprintf "%s\\n" "$?"\n')
 broker.stdin.flush()
 rc=int(broker.stdout.readline().strip())
 output=logfile.read_text()
 assert rc==0,(m,rc,output)
 if m in mods:assert not output,m
for m in mods+['FiniteAudit']:run(m)
audit=(logs/'FiniteAudit.log').read_text();names=(work/'declaration-names.txt').read_text().splitlines()
blocks=re.findall(r'AUDIT (\w+) ([^\n]+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS (.*?)\n',audit,re.S)
assert len(blocks)==len(names)==len(set(names))
assert set(b[1] for b in blocks)==set(names)
for _,n,_,axs,flags in blocks:
 assert flags==('unsafe=false partial=true axiom=false' if n=='Polyomino57.attachCheck._unsafe_rec' else 'unsafe=false partial=false axiom=false'),(n,flags)
 assert set(re.findall(r'[A-Za-z][A-Za-z.]*',axs))<=set(['propext','Classical.choice','Quot.sound'])
(logs/'declaration-inventory.json').write_text(json.dumps([dict(origin=m,name=n,type=t,axioms=a,flags=f) for m,n,t,a,f in blocks],indent=2)+'\n')
checks_source = """import Completed
import Large16
import PackedFull
import Lean
set_option autoImplicit false
set_option linter.auxLemma false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #[MODS]
  for i in [:env.header.moduleNames.size] do
    if mods.contains env.header.moduleNames[i]! then
      for n in env.header.moduleData[i]!.constNames do
        logInfo m!"CHECK_NAME {n}"
        let id := mkIdent n
        elabCommand (← `(command| #check $id))
        elabCommand (← `(command| #print axioms $id))
""".replace('MODS', ', '.join('`'+m for m in mods))
(work/'ExhaustiveChecks.lean').write_text(checks_source)
run('ExhaustiveChecks')
reports=[json.loads(s) for s in (L/'runs.jsonl').read_text().splitlines()]
assert all(r['rc']==0 and r['kill_reason'] is None and r['peak_group_rss']<2800*1024**2 and r['seconds']<230 and r['interval_seconds']==.045 for r in reports)
out=dict(status='PASS_PACKED_SOUNDNESS_AND_LARGEST_FULLMASK_SLICE_37_CASES_33_RESIDUAL',FiniteCases_closed=False,unconditional_UniversalContainer=False,credit=0,additional=5,total=35,origin_declarations=len(names),modules=len(mods),fresh_source_extraction=True,consumed_candidate_oleans=False,all_types_axioms_origins_safety_audited=True,allowed_axioms=['propext','Classical.choice','Quot.sound'],inherited_flag_exception='Polyomino57.attachCheck._unsafe_rec partial=true unsafe=false',build_reports=reports,seconds=time.monotonic()-t)
(logs/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

broker.stdin.write("exit\n");broker.stdin.flush();assert broker.wait()==0
