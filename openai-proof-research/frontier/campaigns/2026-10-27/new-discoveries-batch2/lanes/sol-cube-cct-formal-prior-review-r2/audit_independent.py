import pathlib,json,re,hashlib,collections
L=pathlib.Path(__file__).parent;R=L/'replay'
raw=(R/'Audit.log').read_text();parts=raw.split('DECL|');assert not parts[0].strip()
out=[];allow={'propext','Classical.choice','Quot.sound'}
for block in parts[1:]:
 lines=block.splitlines();header=lines[0].split('|');assert len(header)==5 and header[1]=='ORIGIN' and header[3:] == ['UNSAFE','false']
 name,origin=header[0],header[2];assert origin in ['Finite','Cube','Endpoint']
 assert lines[1].startswith('SAFETY|'+name+'|');safety=lines[1].split('|')[2]
 assert safety in ['nondefinition','Lean.DefinitionSafety.safe']
 axstart=block.rfind("\n'"+name+"'");assert axstart>0
 typ='\n'.join(lines[2:])[:0] # actual boundary below, not a bounded prefix
 body=block[block.index('\n',block.index('\n')+1)+1:axstart]
 assert body.startswith(name) and ':' in body and '⋯' not in body
 report=block[axstart:].strip()
 if 'does not depend on any axioms' in report: ax=[]
 else:
  assert 'depends on axioms: [' in report and report.endswith(']')
  ax=[re.sub(r'\.\{[^}]+\}','',a.strip()) for a in report.split('[',1)[1][:-1].split(',')]
 assert set(ax)<=allow
 out.append(dict(name=name,origin=origin,safety=safety,unsafe=False,type=body,axioms=ax,type_sha256=hashlib.sha256(body.encode()).hexdigest()))
assert len(out)==134 and len({d['name'] for d in out})==134
assert next(d for d in out if d['name']=='Cube.literal_question66_false')['type'].strip()=='Cube.literal_question66_false : Not Cube.LiteralQuestion66AtFive'
assert {a for d in out for a in d['axioms']}==allow
for m in ['Finite','Cube','Endpoint','Audit']:
 g=json.loads((R/(m+'.guard.json')).read_text());assert g['exit_code']==0 and g['reason'] is None
 assert g['command'][1:5]==['-j1','-M2700','-DwarningAsError=true','-DautoImplicit=false']
 assert g['sampled_peak_group_rss']<=2800*1024**2 and g['wall_seconds']<230
# Every actual full type retained. Lossless shared-parenthesis view for reading redundant elaborated dictionaries.
cache={};defs=[]
def compact(s):
 stack=[''];
 for c in s:
  if c=='(':stack.append('(')
  elif c==')' and len(stack)>1:
   expr=stack.pop()+')'
   if len(expr)>65:
    if expr not in cache:cache[expr]='§'+str(len(defs));defs.append(expr)
    expr=cache[expr]
   stack[-1]+=expr
  else:stack[-1]+=c
 assert len(stack)==1
 return re.sub(r'\s+',' ',stack[0])
short=[d['name']+' | '+d['origin']+' | '+d['safety']+' | '+','.join(d['axioms'])+'\n'+compact(d['type']) for d in out]
expanded=[]
for s in defs:
 expanded.append(re.sub(r'§(\d+)',lambda m:expanded[int(m[1])],s))
for d,s in zip(out,short):
 recovered=re.sub(r'§(\d+)',lambda m:expanded[int(m[1])],s.split('\n',1)[1])
 assert re.sub(r'\s+',' ',recovered).strip()==re.sub(r'\s+',' ',d['type']).strip()
(L/'actual-declarations.json').write_text(json.dumps(out,indent=2))
(L/'audit-reading.txt').write_text('\n'.join(short)+'\nDICTIONARY\n'+'\n'.join('§'+str(i)+' = '+re.sub(r'\s+',' ',s) for i,s in enumerate(defs)))
summary=dict(status='PASS',records=len(out),origins=dict(collections.Counter(d['origin'] for d in out)),axioms=sorted(allow),partial=[],full_types='actual-declarations.json',fresh_audit_sha256=hashlib.sha256(raw.encode()).hexdigest())
(L/'independent-audit.json').write_text(json.dumps(summary,indent=2));print(summary);print('reading bytes',(L/'audit-reading.txt').stat().st_size)
