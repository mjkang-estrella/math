import json,sys,re
from pathlib import Path
p=Path(sys.argv[1]);out=Path(sys.argv[2]);entries=[];current=None;ids=set();refs=set();total=None

def finish():
 assert current is not None
 assert refs <= ids, (current['name'],'dangling expression references')
 assert ids==set(range(len(ids))),(current['name'],'noncontiguous node IDs')
 assert current.get('type_ref') is not None and 'has_body' in current
 current['expression_nodes']=len(ids);entries.append(current.copy())

def records(f):
 pending=None
 for line in f:
  line=line.rstrip('\n')
  if re.match(r'^(DECL |MODULE |UNSAFE |PARTIAL |AXIOMS |TYPE_REF |BODY_REF |BODY_NONE$|NODE |END_DECL$|TOTAL_LOCAL_DECLARATIONS )',line):
   if pending is not None:yield pending
   pending=line
  else:
   assert pending is not None
   pending+=' '+line
 if pending is not None:yield pending

with p.open() as f:
 for line in records(f):
  line=line.rstrip('\n')
  if line.startswith('DECL '):
   assert current is None
   current={'name':line[5:]};ids=set();refs=set()
  elif line.startswith('MODULE '):current['module']=line[7:]
  elif line.startswith('UNSAFE '):
   assert line=='UNSAFE false';current['unsafe']=False
  elif line.startswith('PARTIAL '):
   assert line=='PARTIAL false';current['partial']=False
  elif line.startswith('AXIOMS '):
   names=re.findall(r'[A-Za-z][A-Za-z0-9_.]*',line[7:])
   assert set(names)<={'propext','Classical.choice','Quot.sound'},names
   current['axioms']=names
  elif line.startswith('TYPE_REF '):
   i=int(line[9:]);current['type_ref']=i;refs.add(i)
  elif line.startswith('BODY_REF '):
   i=int(line[9:]);current['has_body']=True;current['body_ref']=i;refs.add(i)
  elif line=='BODY_NONE':current['has_body']=False
  elif line.startswith('NODE '):
   _,i,kind,payload=line.split(' ',3)
   i=int(i);assert i not in ids;ids.add(i)
   assert kind in {'bvar','fvar','mvar','sort','const','app','lam','forallE','letE','lit','mdata','proj'}
   if kind=='app':refs.update(map(int,payload.split()))
   elif kind in {'lam','forallE'}:
    m=re.search(r' (\d+) (\d+) \S+$',payload);assert m,line;refs.update(map(int,m.groups()))
   elif kind=='letE':
    m=re.search(r' (\d+) (\d+) (\d+) (?:true|false)$',payload);assert m,line;refs.update(map(int,m.groups()))
   elif kind in {'mdata','proj'}:refs.add(int(payload.rsplit(' ',1)[1]))
  elif line=='END_DECL':finish();current=None
  elif line.startswith('TOTAL_LOCAL_DECLARATIONS '):total=int(line.split()[1])
  else:assert not line.strip(),line[:200]
assert current is None and total==len(entries) and len({e['name'] for e in entries})==total
counts={m:sum(e['module']==m for e in entries) for m in sorted({e['module'] for e in entries})}
out.write_text(json.dumps({'status':'PASS','declaration_count':total,'module_counts':counts,'declarations':entries},indent=2)+'\n')
print(json.dumps({'declaration_count':total,'module_counts':counts}))
