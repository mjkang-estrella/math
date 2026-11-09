import pathlib,json,re,hashlib,zipfile
r=pathlib.Path(__file__).resolve().parent;p=r/'packet';s=p/'src'
order=zipfile.ZipFile(r/'r6-source.zip').read('module-order.txt').decode().splitlines()
base=[m for m in order if not m.startswith(('MaskPilot','MaskRaw')) and m not in ['MaskBuild','AuditR6','EndpointR6','NormalizedExport']]
# Keep all original definitions, bridges, normalizations unchanged; omit experiments.
d=json.loads((r/'normalized-trimmed.json').read_text());steps=d['steps'][:5000]
db={}
for l in (r/'normalized.cnf').read_text().splitlines():
 if l and l[0] not in 'cp':db[len(db)+1]=list(map(int,l.split()))[:-1]
ninputs=len(db)
db.update({i:c for i,c,h in d['steps']})
def mask(c):
 a=b=0
 for x in c:
  if x>0:a|=1<<(x-1)
  else:b|=1<<(-x-1)
 return a,b
# Independently read frozen theorem source as data, expand old theorem references.
old={}
for f in (r/'inherited/src').glob('Inputs*.lean'):
 for mat in re.finditer(r'theorem inp_(\d+).*? := by\n(.*?)(?=\ndef |\nend )',f.read_text(),re.S):
  old[int(mat[1])]=mat[2].strip()
proofs={}
for f in (r/'inherited/src').glob('NInputs*.lean'):
 for mat in re.finditer(r'def cl_(\d+) : CNF.NClause := (.*?)\ntheorem inp_\d+.*? := by\n(.*?)(?=\ndef |\nend )',f.read_text(),re.S):
  i=int(mat[1]);body=mat[3].strip().replace('\n  ','\n')
  body=re.sub(r'exact Percolation.Replay.inp_(\d+) v hb',lambda m:old[int(m[1])].replace(' v h',' v hb'),body)
  proofs[i]=(mat[2],body)
used=sorted({h for _,_,hs in steps for h in hs if h<=ninputs})
assert all(i in proofs for i in used)
mods=[]
for off in range(0,len(used),40):
 m=f'MaskInputs{off//40:04d}';mods.append(m)
 out=['import MaskChainBuild','namespace Percolation.MaskChain','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
 for i in used[off:off+40]:
  clause,body=proofs[i]
  # numeric clause definition is new, inherited clause contents must match DIMACS
  ns=[(abs(x)-1,x<0) for x in db[i]]
  assert re.sub(r'\s','',clause)== '['+','.join(f'({n},{str(b).lower()})' for n,b in ns)+']'
  body=body.replace(f'cl_{i}',f'inputClause{i}')
  a,b=mask(db[i])
  out += [f'def inputClause{i} : CNF.NClause := {clause}',f'theorem inputList{i} (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause{i} := by', '  '+body.replace('\n','\n  '),f'mask_input "{i}|{a}|{b}"']
 out+=['end Percolation.MaskChain']
 (s/f'{m}.lean').write_text('\n'.join(out)+'\n')
replay=[]
for start in range(0,len(steps),100):
 m=f'MaskChain{start//100:04d}';replay.append(m)
 imports=['MaskChainBuild']+ (mods if start==0 else [replay[-2]])
 rows=[]
 for i,c,hs in steps[start:start+100]:
  f=set(c);parts=[]
  for hid in hs:
   rem=[x for x in db[hid] if x not in f];a,b=mask(db[hid])
   if not rem:parts.append(f'{hid},{a},{b},x,0')
   else:
    assert len(rem)==1
    u=rem[0];f.add(-u);parts.append(f'{hid},{a},{b},{abs(u)-1},{int(u<0)}')
  a,b=mask(c);rows.append(f'{i}|{a}|{b}|'+ ';'.join(parts))
 (s/f'{m}.lean').write_text('\n'.join('import '+x for x in imports)+'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nmask_chain '+json.dumps('\n'.join(rows))+'\n')
(p/'module-order.txt').write_text('\n'.join(base+['MaskChainBuild']+mods+replay)+'\n')
(r/'generation.json').write_text(json.dumps({'used_inputs':len(used),'input_modules':len(mods),'replay_modules':len(replay),'target_steps':len(steps),'hint_uses_1000':sum(len(x[2]) for x in steps[:1000]),'hint_uses_5000':sum(len(x[2]) for x in steps),'last_id':steps[-1][0]},indent=2))
# Fresh driver written here; guard is preserved identically.
