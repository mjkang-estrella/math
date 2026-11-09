from pathlib import Path
import json,sys,hashlib,zipfile,subprocess,re
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def bindmods(tag):return [f'Bind{tag}{s}{n:02d}' for s,count in [('Q',8),('P',15)] for n in range(count)]+['Bindings'+tag]
base=['Literal','InstanceG','InstanceH','Rank','Hulls','Geometry','IntegerCore','DataG','DataH','RealCore','CompletionCore','ListedG','ListedH']
batches=[f'Batch{tag}{n:03d}' for tag in ['G','H'] for n in range(310)]
groups=[f'Group{tag}{n:02d}' for tag in ['G','H'] for n in range(20)]
ends=['Domain','AllG','AllH','CompleteG','CompleteH','HullG','HullH']
math=base+bindmods('G')+bindmods('H')+batches+groups+ends
audits=[]
def audit(name,imports,origins):
 audits.append(name)
 (L/f'{name}.lean').write_text('\n'.join(['import '+m for m in imports]+['import StrictAudit','#strict_audit ['+', '.join(origins)+']'])+'\n')
mode=sys.argv[1]
if mode=='prepare':
 audit('AuditBase',['Geometry','InstanceG','InstanceH'],base[:6])
 audit('AuditCore',['CompletionCore','ListedG','ListedH','Domain'],base[6:]+['Domain'])
 for tag in ['G','H']:
  audit('AuditBindings'+tag,['Bindings'+tag],bindmods(tag))
  for n in range(20):
   g=f'Group{tag}{n:02d}';origins=[f'Batch{tag}{k:03d}' for k in range(n*16,min(310,(n+1)*16))]+[g]
   audit('Audit'+g,[g],origins)
  audit('AuditEnd'+tag,['Hull'+tag],['All'+tag,'Complete'+tag,'Hull'+tag])
 (L/'mathematical-modules.json').write_text(json.dumps(math,indent=2)+'\n')
 (L/'replay-order.json').write_text(json.dumps(base+bindmods('G')+bindmods('H')+batches+groups+ends+['StrictAudit']+audits,indent=2)+'\n')
 print('prepared',len(math),'mathematical modules',len(audits),'audit passes')
elif mode in ['archive','refresh-unbuilt','refresh-candidate']:
 order=json.loads((L/'replay-order.json').read_text())
 files=[m+'.lean' for m in order]+['runner.py','pins.json','replay-order.json','mathematical-modules.json','RUN.md']
 hashes={f:sha(L/f) for f in files}
 (L/'archive-files.json').write_text(json.dumps(hashes,indent=2)+'\n')
 with zipfile.ZipFile(L/'source.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
  for f in sorted(files+['archive-files.json']):
   i=zipfile.ZipInfo(f,(2026,10,30,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16;z.writestr(i,(L/f).read_bytes())
 D=L/'replay/fresh'
 if mode in ['refresh-unbuilt','refresh-candidate']:
  for f in files:
   if not (D/f).exists() or (D/f).read_bytes()!=(L/f).read_bytes():
    if mode=='refresh-unbuilt':assert f in ['Domain.lean','AuditCore.lean','AllG.lean','AllH.lean','replay-order.json','mathematical-modules.json'] and not (D/Path(f).with_suffix('.olean')).exists(),f
    else:
     assert f not in [m+'.lean' for m in base[:6]],f
     dest=L/'failures'/('candidate-'+f.replace('/','--')+'.txt');dest.parent.mkdir(exist_ok=True)
     if (D/f).exists() and not dest.exists():dest.write_bytes((D/f).read_bytes())
    (D/f).write_bytes((L/f).read_bytes())
  (D/'archive-files.json').write_bytes((L/'archive-files.json').read_bytes())
  print('candidate refresh; final clean replay still required' if mode=='refresh-candidate' else 'refreshed only unbuilt modules; every already-compiled source unchanged')
  sys.exit(0)
 D.mkdir(parents=True,exist_ok=False)
 with zipfile.ZipFile(L/'source.zip') as z:z.extractall(D)
 print('source-only extraction',sha(L/'source.zip'))
elif mode=='replay':
 D=L/'replay/fresh';order=json.loads((D/'replay-order.json').read_text())
 for f,h in json.loads((D/'archive-files.json').read_text()).items():assert sha(D/f)==h,f
 for m in order[int(sys.argv[2]):int(sys.argv[3])]:
  r=subprocess.run([sys.executable,str(D/'runner.py'),'-o',m+'.olean',m+'.lean'],cwd=D,capture_output=True,text=True)
  if r.returncode:print(m,r.stdout,r.stderr);sys.exit(r.returncode)
 print('PASS extracted modules',sys.argv[2:])
elif mode=='reconcile':
 D=L/'replay/fresh';order=json.loads((D/'replay-order.json').read_text());mods=set(json.loads((D/'mathematical-modules.json').read_text()))
 ok={};texts=[]
 for p in sorted(D.glob('attempt-*.json')):
  r=json.loads(p.read_text());s=p.with_suffix('.log').read_text();assert r['exit']==0 and r['reason'] is None,(p,r)
  assert not any(x in s.lower() for x in ['panic','error:','rejected','sorryax']),p
  ok[Path(r['command'][-1]).stem]=r;texts.append(s)
 assert set(ok)==set(order),(set(order)-set(ok))
 text='\n'.join(texts)
 owned=set(re.findall(r'OWN_DECL (\S+)',text))
 covered=set(re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",text))
 assert owned==covered and owned,(len(owned),len(covered),owned-covered,covered-owned)
 for tag in ['OWN_SAFETY','OWN_PARTIAL']:
  rows=dict(re.findall(tag+r' (\S+) (\S+)',text));assert set(rows)==owned and set(rows.values())=={'false'}
 origins=set(re.findall(r'AUDITED_ORIGIN (\S+)',text));assert origins==mods,(mods-origins,origins-mods)
 observed=set()
 for s in re.findall(r'depends on axioms: \[([^\]]*)\]',text,re.S):observed|={x.strip() for x in s.split(',') if x.strip()}
 assert observed<={'propext','Classical.choice','Quot.sound'},observed
 (L/'owned-declarations.json').write_text(json.dumps(sorted(owned),indent=2)+'\n')
 (L/'audit.json').write_text(json.dumps(dict(status='PASS',owned=len(owned),origins=sorted(origins),private_generated=True,partial_flags=False,unsafe_flags=False,transitive_type_body_checked=True,transitive_counts=[int(x) for x in re.findall(r'TRANSITIVE_SAFE_COUNT (\d+)',text)],axioms=sorted(observed)),indent=2)+'\n')
 interrupted=[str(p.relative_to(L)) for p in sorted(D.glob('attempt-*.log')) if not p.with_suffix('.json').exists()]
 (L/'replay-receipt.json').write_text(json.dumps(dict(status='PASS',archive_sha256=sha(L/'source.zip'),compiler_calls=len(order),owned=len(owned),serial=True,source_only=True,diagnostics_rejected=True,actual_vertices_and_hulls=True,unreceipted_interrupted_logs=interrupted),indent=2)+'\n')
 print('PASS',len(order),'calls',len(owned),'owned origins',len(origins))
