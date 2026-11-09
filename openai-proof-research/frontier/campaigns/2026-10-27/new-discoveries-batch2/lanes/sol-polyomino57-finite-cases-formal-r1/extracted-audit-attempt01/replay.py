from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time,resource,signal
resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((L/'pins.json').read_text())
assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
assert subprocess.check_output([pins['lean_binary'],'-j1','--version'],text=True).strip()==pins['lean_version']
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
 q=subprocess.run([sys.executable,str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=work,capture_output=True,text=True)
 (logs/(m+'.log')).write_text(q.stdout+q.stderr)
 assert q.returncode==0,(m,q.stdout,q.stderr)
 if m in mods:assert not q.stdout and not q.stderr,m
for m in mods+['FiniteAudit']:run(m)
audit=(logs/'FiniteAudit.log').read_text();names=(work/'declaration-names.txt').read_text().splitlines()
blocks=re.findall(r'AUDIT (\w+) ([^\n]+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS (.*?)\n',audit,re.S)
assert len(blocks)==len(names)==len(set(names))
assert set(b[1] for b in blocks)==set(names)
for _,n,_,axs,flags in blocks:
 assert flags==('unsafe=false partial=true axiom=false' if n=='Polyomino57.attachCheck._unsafe_rec' else 'unsafe=false partial=false axiom=false'),(n,flags)
 assert set(re.findall(r'[A-Za-z][A-Za-z.]*',axs))<=set(['propext','Classical.choice','Quot.sound'])
(logs/'declaration-inventory.json').write_text(json.dumps([dict(origin=m,name=n,type=t,axioms=a,flags=f) for m,n,t,a,f in blocks],indent=2)+'\n')
(work/'ExhaustiveChecks.lean').write_text('import Completed\nimport Large16\nset_option autoImplicit false\nset_option linter.auxLemma false\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in names))
run('ExhaustiveChecks')
reports=[json.loads(s) for s in (L/'runs.jsonl').read_text().splitlines()]
assert all(r['rc']==0 and r['kill_reason'] is None and r['peak_group_rss']<2800*1024**2 and r['seconds']<230 and r['interval_seconds']==.045 for r in reports)
out=dict(status='PASS_37_LITERAL_CASES_AND_EXACT_33_CASE_RESIDUAL',FiniteCases_closed=False,unconditional_UniversalContainer=False,credit=0,additional=5,total=35,origin_declarations=len(names),modules=len(mods),fresh_source_extraction=True,consumed_candidate_oleans=False,all_types_axioms_origins_safety_audited=True,allowed_axioms=['propext','Classical.choice','Quot.sound'],inherited_flag_exception='Polyomino57.attachCheck._unsafe_rec partial=true unsafe=false',build_reports=reports,seconds=time.monotonic()-t)
(logs/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
