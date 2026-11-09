"""Streaming exhaustive post-replay verifier. Run through helper_guard.py."""
from pathlib import Path
import json,re,hashlib,sys
R=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=json.loads((R/'replay-modules.json').read_text());audits=json.loads((R/'audit-modules.json').read_text())
assert len(mods)==437 and len(audits)==22 and len(set(mods+audits))==459
pins=json.loads((R/'pins.json').read_text());assert sha(Path(pins['lean']))==pins['lean_sha256']
heads={}
for row in pins['packages']:
 g=Path(pins['formal'])/'.lake/packages'/row['name']/'.git'
 h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  ref=h[5:]
  if (g/ref).exists():h=(g/ref).read_text().strip()
  else:h=dict(line.split()[::-1] for line in (g/'packed-refs').read_text().splitlines() if line and not line.startswith(('#','^')))[ref]
 assert h==row['revision'];heads[row['name']]=h
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
   s=raw.strip();assert '⋯' not in s
   if s.startswith('DECL|'):
    q=s.split('|');assert len(q)==6 and q[2]=='ORIGIN' and q[4]=='UNSAFE' and q[5]=='false';current=q[1];assert current not in names;names[current]=q[3]
   elif s.startswith('SAFETY|'):
    _,n,v=s.split('|');assert n==current and v in ['Lean.DefinitionSafety.safe','nondefinition'];safety.add(n)
   elif current and (s==current or s.startswith(current+' ') or s.startswith(current+'.{') or s.startswith('@'+current+' ') or s.startswith('@'+current+'.{')):types.add(current)
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
    a=re.sub(r'\.\{[^}]*\}','',q.split('depends on axioms:',1)[1]);vals=set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a));assert vals<=allowed,(n,vals)
   all_axioms|=vals;axioms.add(n)
 assert pending is None
assert set(names)==types==safety==axioms,(len(names),len(types),len(safety),len(axioms))
assert len(names)==35654 and set(names.values())==set(mods)-{'Dag168'}
assert sum(o in ['Reduction','Symmetry','Source','Expansion'] for o in names.values())==59
assert sum(bool(re.fullmatch(r'FloorCertificate\.node_\d+',n)) for n in names)==1329
assert all(n in names for n in ['Assembly.literal_endpoint','Assembly.sorted_clamped_bound','Assembly.query_of_neg_bound','Assembly.n22671'])
for m in mods:
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|partial)\b',(R/(m.replace('.','/')+'.lean')).read_text())
digest=hashlib.sha256('\n'.join(sorted(names)).encode()).hexdigest()
assert digest=='7abfdce5f2b7e1d6ba7df2fc0de7ee9a96faa975f113e04b512bfd42008a668b'
out=dict(status='PASS',endpoint='Assembly.literal_endpoint : FloorSums.LiteralEndpoint',source_modules=len(mods),audit_partitions=len(audits),serial_invocations=len(guards),actual_declarations=len(names),origins=len(set(names.values())),empty_origin_module='Dag168',all_types_safety_transitive_axioms_covered=True,safe_nonpartial=True,allowed_axioms=sorted(all_axioms),inherited_source_declarations=59,arithmetic_implications=1329,strict_fresh_replay=True,package_heads=heads,max_sampled_group_RSS=max(g['sampled_peak_group_rss'] for g in guards),max_invocation_wall=max(g['wall_seconds'] for g in guards),names_sha256=digest)
(R/'full-audit-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
