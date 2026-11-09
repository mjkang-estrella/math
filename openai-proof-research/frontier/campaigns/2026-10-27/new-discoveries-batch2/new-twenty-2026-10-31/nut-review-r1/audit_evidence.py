import pathlib,resource,os,json,re,zipfile,difflib,hashlib
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
l=pathlib.Path(__file__).resolve().parent;b=l.parent;r=b/'nut-formal-r7q';f=r/'formal'
# independent textual import closure
seen=set()
def visit(n):
 if n in seen:return
 p=f/(n+'.lean')
 if not p.exists():return
 seen.add(n)
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for m in line[7:].split():visit(m)
visit('Nut8Final');assert not any(x.startswith('Audit') for x in seen)
claimed=json.loads((r/'closure.json').read_text());assert set(claimed)==seen
counts={'MODULE':0,'FLAGS':0,'BODY':0,'AXIOMS':0,'LOCAL_TOTAL':0};mods=set();names=set();duplicates=[];bad=[];axioms=set();totals=[]
with (r/'audit.log').open() as x:
 for line in x:
  for p in counts:
   if line.startswith(p+' '):counts[p]+=1
  if line.startswith('MODULE '):
   m=re.search(r'MODULE some \((\w+)\) DECL (.*?) TYPE',line)
   if m:mods.add(m[1]);duplicates.extend([m[2]] if m[2] in names else []);names.add(m[2])
  if line.startswith('FLAGS ') and line.strip()!='FLAGS unsafe=false partial=false axiom=false':bad.append(line)
  if line.startswith('AXIOMS '):
   m=re.search(r'\[(.*?)\]',line)
   if m:axioms.update(z.strip() for z in m[1].split(',') if z.strip())
  if line.startswith('LOCAL_TOTAL '):totals.append(int(line.split()[1]))
print('audit diagnostics',len(names),counts,'bad',bad[:3],'missing modules',seen-mods,'extra modules',mods-seen,flush=True)
assert counts['MODULE']==46045 and counts['FLAGS']==46045 and not bad and mods==seen
print('duplicates',duplicates,flush=True)
assert axioms<= {'propext','Classical.choice','Quot.sound'}
# inspect real diffs from initial packet, not narrative descriptions
changes={}
with zipfile.ZipFile(r/'nut-r7q-initial-source.zip') as z,zipfile.ZipFile(r/'nut-r7q-source.zip') as y:
 for n in z.namelist():
  if n.startswith('formal/') and n.endswith('.lean') and z.read(n)!=y.read(n):
   changes[n]=''.join(difflib.unified_diff(z.read(n).decode().splitlines(True),y.read(n).decode().splitlines(True)))
assert len(changes)==6
assert (f/'NutInterface.lean').read_bytes()==(b/'nut-interface-r5/NutInterface.lean').read_bytes()
for n in ['162','163','164','165','166']:
 with zipfile.ZipFile(r/'nut-r7q-initial-source.zip') as z:assert z.read('formal/FiniteSupport'+n+'.lean').replace(b'maxRecDepth 4096',b'maxRecDepth 8192')==(f/('FiniteSupport'+n+'.lean')).read_bytes()
# Record exact receipts and status, not only summary
v=json.loads((r/'development-validation.json').read_text());neg=json.loads((r/'negative-controls-receipts.json').read_text())
parent=json.loads((b/'nut-parent-final-r1/replay/replay-state.json').read_text())
(l/'evidence-audit.json').write_text(json.dumps({'closure_count':len(seen),'audit_modules_equal_closure':mods==seen,'counts':counts,'unique_printed_names':len(names),'duplicate_printed_names':duplicates,'axioms':sorted(axioms),'bad_flags':bad,'diffs':changes,'fixed_interface_identical':True,'development_validation_keys':list(v),'negative_control_keys':list(neg),'parent_replay_snapshot':parent},indent=2)+'\n')
print('closure',len(seen),'audit',len(names),'axioms',axioms,'changes',list(changes));print(changes['formal/PerSupport.lean'])
