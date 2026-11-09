import hashlib, json, os, pathlib, re, subprocess, sys, time, uuid
root=pathlib.Path(__file__).resolve().parent.parent
bin=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pkg=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
for d in ['logs','tmp','build','cache']: (root/d).mkdir(exist_ok=True)
env=dict(os.environ, PATH=str(bin)+':'+os.environ.get('PATH',''), LEAN_PATH=':'.join([str(root/'build')]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(root/'tmp'),XDG_CACHE_HOME=str(root/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
modules=['Dynamics','Reduction','SourceSemantics','Cardinality','Endpoint','Controls','Audit']
manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (root/'formal').glob('*.lean')}
fingerprint=hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest()
def run(label,args,fail=False):
 log=root/'logs'/f'{label}-{time.time_ns()}-{uuid.uuid4().hex[:6]}.log'
 with log.open('w') as f:
  p=subprocess.run(['/usr/bin/time','-v',sys.executable,'-I',str(root/'scripts/cap.py')]+list(map(str,args)),cwd=root/'formal',env=env,stdout=f,stderr=subprocess.STDOUT)
 s=log.read_text()
 if fail:
  assert p.returncode!=0 and 'error:' in s,(label,s)
 else:
  assert p.returncode==0 and 'error:' not in s,(label,s)
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
audit=(root/records['Audit']['lean']).read_text()
rows=re.findall(r'DECL (\S+) MODULE (\S+) UNSAFE false PARTIAL false IMPLEMENTED_BY none EXTERN false AXIOMS \[([^\]]*)\]',audit)
total=int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',audit)[1])
assert len(rows)==total
allowed={'propext','Classical.choice','Quot.sound'}
assert all({x.strip() for x in row[2].split(',') if x.strip()}<=allowed for row in rows)
# Independently compute local module closure, including all imports from Controls.
sources={p.stem:p.read_text() for p in (root/'formal').glob('*.lean')}
closure=set(); work=['Controls']
while work:
 m=work.pop()
 if m in closure:continue
 closure.add(m)
 work += [i for i in re.findall(r'^import (\S+)',sources[m],re.M) if i in sources]
assert closure==set(m for _,m,_ in rows)==set(re.findall(r'AUDIT_MODULE (\S+)',audit))
# Three expected compilation failures. No false theorem enters the certificate.
negatives={
 'WrongWeight': 'import Controls\nexample : ChanLevine.Controls.wrongWeight ChanLevine.Controls.start = ChanLevine.Controls.wrongWeight (ChanLevine.fire ChanLevine.Controls.start 0) := by decide\n',
 'WrongRecurrence': 'import Controls\nexample : ChanLevine.Recurrent (ChanLevine.SignedConfig.mk (fun _ : ZMod 3 => 0) (fun _ => true)) := by\n  refine ⟨⟨_, 0, ?_, rfl⟩, ?_⟩\n  · decide\n  · intro d h; exact Relation.ReflTransGen.refl\n',
 'WrongDifferentGCD': 'import Controls\nexample : (26 : ℕ) = 24 := by decide\n'}
for name,src in negatives.items():
 p=root/'tmp'/f'{name}.lean';p.write_text(src)
 run('negative-'+name,[bin/'lean','-j1','-M3500','-DwarningAsError=true',p],fail=True)
run('regression',[sys.executable,'-I',root/'scripts/regression.py'])
report={'status':'PASS','modules':records,'source_hashes':manifest,'audit_declarations':total,'audit_local_closure':sorted(closure),'axioms':sorted(allowed),'negative_controls':list(negatives),'regression_cases':18,'endpoint_unconditional':False,'remaining_props':['CycleTestBridge','CanonicalTest','ConnectedFibres','RotationCount','UnitCount','ArithmeticOrbit','AmbientBridge']}
(root/'logs/replay-result.json').write_text(json.dumps(report,indent=2))
print('PASS strict serial replay; unconditional endpoint remains unproved',flush=True)
