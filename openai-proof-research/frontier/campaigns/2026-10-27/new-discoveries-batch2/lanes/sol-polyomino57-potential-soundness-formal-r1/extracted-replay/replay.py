"""Source-only replay. Run in an extracted component directory."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
L=Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((L/'pins.json').read_text())
assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
assert subprocess.check_output([pins['lean_binary'],'--version'],text=True).strip()==pins['lean_version']
def revision(repo):
 g=repo/'.git'
 if g.is_file():g=(repo/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(g/'HEAD').read_text().strip()
 if not head.startswith('ref: '):return head
 ref=head[5:]
 if (g/ref).exists():return (g/ref).read_text().strip()
 for line in (g/'packed-refs').read_text().splitlines():
  if line.endswith(' '+ref):return line.split()[0]
 raise AssertionError(str(repo))
for pkg in pins['packages'].values():assert revision(Path(pkg['path']))==pkg['revision']
manifest=json.loads((L/'source-manifest.json').read_text())
for f,v in manifest.items():
 p=L/f
 assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes'],f
work=L/'fresh-build'
assert not work.exists(),'Fresh work directory required'
work.mkdir()
logs=L/'verification';logs.mkdir()
mods=['Grid','Potential','Bridge']
for m in mods+['OriginAudit']:
 p=L/'formal'/(m+'.lean')
 if m!='OriginAudit':assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',p.read_text())
 (work/p.name).write_bytes(p.read_bytes())
start=time.monotonic()
def run(m):
 q=subprocess.run([sys.executable,str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=work,capture_output=True,text=True)
 (logs/(m+'.log')).write_text(q.stdout+q.stderr)
 assert q.returncode==0,(m,q.stdout,q.stderr)
 if m in mods:assert not q.stdout and not q.stderr
for m in mods+['OriginAudit']:run(m)
names=(work/'declaration-names.txt').read_text().splitlines()
audit=(logs/'OriginAudit.log').read_text()
assert f'AUDIT_TOTAL {len(names)}' in audit and names
assert len(set(names))==len(names)
blocks=re.findall(r'AUDIT (\w+) ([^\n]+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS (.*?)\n',audit,re.S)
assert len(blocks)==len(names)
assert set(b[1] for b in blocks)==set(names)
for _,_,_,axs,flags in blocks:
 assert flags=='unsafe=false partial=false axiom=false'
 assert set(re.findall(r'[A-Za-z][A-Za-z.]*',axs))<=set(['propext','Classical.choice','Quot.sound'])
(logs/'declaration-inventory.json').write_text(json.dumps([dict(origin=m,name=n,type=t,axioms=a,flags=f) for m,n,t,a,f in blocks],indent=2)+'\n')
# Actual Lean commands, not a substitute text scan, for every origin declaration.
(work/'ExhaustiveChecks.lean').write_text('import Bridge\nset_option autoImplicit false\nset_option linter.auxLemma false\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in names))
run('ExhaustiveChecks')
reports=[json.loads(s) for s in (L/'runs.jsonl').read_text().splitlines()]
assert all(r['rc']==0 and r['kill_reason'] is None and r['peak_group_rss']<2800*1024**2 and r['seconds']<240 and r['interval_seconds']==.045 for r in reports)
receipt=dict(status='PASS_GENERIC_POTENTIAL_SOUNDNESS_AND_GRID_BRIDGE',credit=0,counts=dict(additional=5,total=35),fullSourceEndpoint=False,source_only_extraction=True,consumed_candidate_oleans=False,source_hashes={m:sha(work/(m+'.lean')) for m in mods},pins_sha256=sha(L/'pins.json'),manifest_sha256=sha(L/'source-manifest.json'),origin_declarations=len(names),exhaustive_check_and_print_axioms=True,origin_and_unsafe_audits=True,allowed_axioms=['propext','Classical.choice','Quot.sound'],jobs=1,warningAsError=True,autoImplicit=False,monitor_interval_seconds=.045,rss_kill_MiB=2800,wall_kill_seconds=230,peak_group_rss=max(r['peak_group_rss'] for r in reports),seconds=time.monotonic()-start,build_reports=reports)
(logs/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
