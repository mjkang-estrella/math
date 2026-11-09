from pathlib import Path
import json,re,hashlib,tarfile,gzip
L=Path(__file__).resolve().parent;R=L/'replay'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
mods=json.loads((R/'replay-modules.json').read_text());audits=json.loads((R/'audit-modules.json').read_text())
pins=json.loads((L/'pins-independent.json').read_text())
assert sha(Path(pins['lean']))==pins['lean_sha256']
guards=[]
for m in mods+audits:
 g=json.loads((R/'logs'/(m+'.guard.json')).read_text());assert g['exit_code']==0 and g['reason'] is None,(m,g)
 assert g['command'][0]==pins['lean'] and all(x in g['command'] for x in ['-j1','-M2700','-DwarningAsError=true','-DautoImplicit=false'])
 assert g['sampled_peak_group_rss']<=2800*1024**2 and g['wall_seconds']<=230
 guards.append(g)
names={};types=set();safety=set();axioms=set();allowed={'propext','Classical.choice','Quot.sound'};all_axioms=set()
for m in audits:
 current=None;pending=None
 with (R/'logs'/(m+'.log')).open() as f:
  for raw in f:
   s=raw.strip()
   if s.startswith('DECL|'):
    q=s.split('|');assert len(q)==6 and q[2]=='ORIGIN' and q[4]=='UNSAFE' and q[5]=='false';current=q[1];assert current not in names;names[current]=q[3]
   elif s.startswith('SAFETY|'):
    _,n,v=s.split('|');assert n==current and v in ['Lean.DefinitionSafety.safe','nondefinition'];safety.add(n)
   elif current and (s==current or s.startswith(current+' ') or s.startswith(current+'.{') or s.startswith('@'+current+' ') or s.startswith('@'+current+'.{')):
    types.add(current)
   if pending is not None:
    pending+=s
    if ']' not in pending:continue
    q=pending;pending=None
   elif s.startswith("'") and ('depends on axioms:' in s or 'does not depend on any axioms' in s):
    if 'depends on axioms:' in s and ']' not in s:pending=s;continue
    q=s
   else:continue
   n=q.split("'",2)[1];assert n==current
   if 'does not depend on any axioms' in q:vals=set()
   else:
    a=q.split('depends on axioms:',1)[1];a=re.sub(r'\.\{[^}]*\}','',a);vals=set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a));assert vals<=allowed,(n,vals)
   all_axioms|=vals;axioms.add(n)
 assert pending is None
assert set(names)==types==safety==axioms,(len(names),len(types),len(safety),len(axioms),list(set(names)-types)[:5])
assert len(names)==35654 and set(names.values())==set(mods)-{'Dag168'}
assert sum(o in ['Reduction','Symmetry','Source','Expansion'] for o in names.values())==59
I=json.loads((L/'frozen/assembly-inventory.json').read_text())
assert all('Assembly.n'+str(d['node']) in names for d in I)
assert sum(n.startswith('FloorCertificate.node_') for n in names)==1329
assert all(n in names for n in ['Assembly.literal_endpoint','Assembly.sorted_clamped_bound','Assembly.query_of_neg_bound','Assembly.n22671'])
with tarfile.open(L/'source-only.tar.gz') as t:
 members=t.getmembers();assert len(members)==499
 for m in members:
  assert m.isfile() and m.uid==m.gid==m.mtime==0 and m.mode==0o644
  assert Path(m.name).suffix not in ['.olean','.ilean','.ir']
  h=hashlib.sha256(t.extractfile(m).read()).hexdigest();assert h==sha(R/m.name)
 # Recreate canonical bytes from member metadata and extracted source.
 with (L/'reproduced-source-only.tar.gz').open('wb') as raw:
  with gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0) as gz:
   with tarfile.open(fileobj=gz,mode='w') as out:
    for m in members:
     with (R/m.name).open('rb') as f:out.addfile(m,f)
assert sha(L/'reproduced-source-only.tar.gz')==sha(L/'source-only.tar.gz')=='17ba800adb3154f5c3929ef076c47b9d1f0adaace1576793faa4154ff19be13f'
out=dict(status='PASS',source_modules=len(mods),audit_partitions=len(audits),actual_declarations=len(names),origins=len(set(names.values())),empty_origin_module='Dag168',all_types_safety_transitive_axioms_covered=True,allowed_axioms=sorted(all_axioms),inherited_source_declarations=59,arithmetic_implications=1329,strict_fresh_replay=True,archive_byte_reproduction=True,max_sampled_group_RSS=max(g['sampled_peak_group_rss'] for g in guards),max_invocation_wall=max(g['wall_seconds'] for g in guards),names_sha256=hashlib.sha256('\n'.join(sorted(names)).encode()).hexdigest())
(L/'independent-replay-receipt.json').write_text(json.dumps(out,indent=2));print(out)
