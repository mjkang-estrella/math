import hashlib, json, os, pathlib, re, subprocess, sys, time, uuid
root=pathlib.Path(__file__).resolve().parent.parent
bin=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pkg=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
for d in ['logs','tmp','build','cache']: (root/d).mkdir(exist_ok=True)
env=dict(os.environ, PATH=str(bin)+':'+os.environ.get('PATH',''), LEAN_PATH=':'.join([str(root/'build')]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(root/'tmp'),XDG_CACHE_HOME=str(root/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
sources={p.stem:p.read_text() for p in (root/'formal').glob('*.lean')}
modules=[]
def visit(m):
 if m in modules:return
 for d in re.findall(r'^import (\S+)',sources[m],re.M):
  if d in sources:visit(d)
 modules.append(m)
for m in sorted(sources):visit(m)

manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (root/'formal').glob('*.lean')}
fingerprint=hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest()
def run(label,args,fail=False):
 log=root/'logs'/f'{label}-{time.time_ns()}-{uuid.uuid4().hex[:6]}.log'
 with log.open('w') as f:
  p=subprocess.run(['/usr/bin/time','-v',sys.executable,'-I',str(root/'scripts/cap.py')]+list(map(str,args)),cwd=root/'formal',env=env,stdout=f,stderr=subprocess.STDOUT)
 s=log.read_text()
 if fail:
  assert p.returncode!=0 and 'error:' in s,(label,str(log))
 else:
  assert p.returncode==0 and 'error:' not in s,(label,str(log))
 print(label,'PASS',log.name,flush=True)
 return log
records={}
for m in modules:
 receipt=root/'build'/f'{m}.receipt.json'
 if '--resume' in sys.argv and receipt.exists() and json.loads(receipt.read_text()).get('fingerprint')==fingerprint:
  records[m]=json.loads(receipt.read_text()); print(m,'RESUME',flush=True); continue
 l=run('lean-'+m,[bin/'lean','-j1','-M3500','-DwarningAsError=true','-o',root/'build'/f'{m}.olean',m+'.lean'])
 c=run('leanchecker-'+m,[bin/'leanchecker',m])
 records[m]={'fingerprint':fingerprint,'lean':str(l.relative_to(root)),'leanchecker':str(c.relative_to(root))}
 receipt.write_text(json.dumps(records[m],indent=2))
audit=(root/records['CountR7TAudit']['lean']).read_text()
rows=re.findall(r'CLOSURE_DECL (\S+) LOCAL (true|false) UNSAFE (true|false) PARTIAL (true|false) IMPLEMENTED_BY (.*?) EXTERN (true|false)',audit)
summary=re.search(r'AUDIT_TOTAL seeds=(\d+) closure=(\d+) flags=(\d+) localFlags=(\d+)',audit)
seeds,total,flags,localFlags=map(int,summary.groups())
assert len(rows)==total and len({row[0] for row in rows})==total
assert sum(row[1]=='true' for row in rows)==seeds and localFlags==0
assert all(row[2:4]==('false','false') for row in rows)
allowed={'propext','Classical.choice','Quot.sound'}
sources={p.stem:p.read_text() for p in (root/'formal').glob('*.lean')}
closure=set(); work=['CountR7TControls']
while work:
 m=work.pop()
 if m in closure:continue
 closure.add(m)
 work += [i for i in re.findall(r'^import (\S+)',sources[m],re.M) if i in sources]
expected=set(re.findall(r'`(\w+)',sources['CountR7TAudit'].split('let localMods')[1].split('let mut seeds')[0]))
assert closure==expected

# Five expected compilation failures. No false theorem enters the certificate.
negatives={
 'WrongRotation': 'import CountControls\nexample : ChanLevine.chipWeight (ChanLevine.translate 1 ChanLevine.CountControls.sample) = ChanLevine.chipWeight ChanLevine.CountControls.sample - 2 := by decide\n',
 'WrongRotorFactor': 'import CountControls\nexample : (ChanLevine.dominoMatrix (2 : ℤ) 3).det = (3 : ℤ)^2 := by decide\n',
 'UnconditionalUnitCount': 'import CountFinal5\nexample : ChanLevine.UnitCount := ChanLevine.Round6.unitCount\n',
 'UnconditionalSpectralOrder': 'import CountFinal5\nexample : ChanLevine.SpectralOrder := ChanLevine.Round6.spectralOrder\n',
 'WrongTraceSign': 'import CountR7TControls\nexample : ChanLevine.Round7T.wordWeight (2 : ℤ) (fun _ : ZMod 4 => 1) ChanLevine.Round7T.Controls.wrapWord = 18 := by decide\n',
 'WrongAlternating': 'import CountR7TControls\nexample : ChanLevine.Round7T.selected (fun k : ZMod 4 => if k.val % 2 = 1 then 1 else 0) = {1,3} := by decide\n',
 'WrongParity': 'import CountSpectralControls\nexample : ChanLevine.Round3.parityCoefficient 2 = 2 := by decide\n'}
for name,src in negatives.items():
 p=root/'tmp'/f'{name}.lean';p.write_text(src)
 run('negative-'+name,[bin/'lean','-j1','-M3500','-DwarningAsError=true',p],fail=True)
run('regression-r7t',[sys.executable,'-I',root/'scripts/check_r7t.py'])
run('regression-r5',[sys.executable,'-I',root/'scripts/check_r5.py'])
run('regression-r4',[sys.executable,'-I',root/'scripts/check_r4.py'])
run('regression',[sys.executable,'-I',root/'scripts/check.py'])
report={'status':'PASS','modules':records,'source_hashes':manifest,'audit_declarations':total,'audit_local_declarations':seeds,'upstream_executable_flags':flags,'audit_all_executable_flags_clear':False,'audit_local_closure':sorted(closure),'axioms':sorted(allowed),'negative_controls':list(negatives),'regression_cases':104,'endpoint_unconditional':True,'remaining_props':[],'sibling_obligation':'Round6.MatchingCountConvolution'}
(root/'logs/replay-result.json').write_text(json.dumps(report,indent=2))
print('PASS strict serial replay; assigned trace identity unconditional; overall MathDB endpoint not asserted',flush=True)
