from pathlib import Path
import json,re,hashlib,zipfile,shutil,textwrap
r=Path(__file__).resolve().parent;p=r/'packet';s=p/'src'
d=json.loads((r/'normalized-trimmed.json').read_text());steps=d['steps'];target=129671
original=zipfile.ZipFile(r/'r7-source.zip').read('module-order.txt').decode().splitlines()
db={}
for l in (r/'normalized.cnf').read_text().splitlines():
 if l and l[0] not in 'cp':db[len(db)+1]=list(map(int,l.split()))[:-1]
ninputs=len(db);assert ninputs==d['inputs'];db.update({i:c for i,c,h in steps})
def mask(c):
 a=b=0
 for x in c:
  if x>0:a|=1<<(x-1)
  else:b|=1<<(-x-1)
 return a,b
old={}
for f in (r/'historical/src').glob('Inputs*.lean'):
 for m in re.finditer(r'theorem inp_(\d+).*? := by\n(.*?)(?=\ndef |\nend )',f.read_text(),re.S):old[int(m[1])]=textwrap.dedent(m[2]).strip()
proofs={}
for f in (r/'historical/src').glob('NInputs*.lean'):
 for m in re.finditer(r'def cl_(\d+) : CNF.NClause := (.*?)\ntheorem inp_\d+.*? := by\n(.*?)(?=\ndef |\nend )',f.read_text(),re.S):
  body=m[3].strip().replace('\n  ','\n');body=re.sub(r'exact Percolation.Replay.inp_(\d+) v hb',lambda t:old[int(t[1])].replace(' v h',' v hb'),body);proofs[int(m[1])]=(m[2],body)
used0={h for _,_,hs in steps[:5000] for h in hs if h<=ninputs}
# Separate input batches for each required window, so timings charge only needed input proofs.
newmods=[];bounds=[5000,13561,14561,18561,129671];meta={};used=set(used0);previous='MaskChain0049';chain=[]
for lo,hi in zip(bounds,bounds[1:]):
 needed=sorted({h for _,_,hs in steps[lo:hi] for h in hs if h<=ninputs}-used);imods=[]
 for off in range(0,len(needed),40):
  name=f'R8Inputs{lo}_{off//40:03d}';imods.append(name);out=['import MaskChainBuild','namespace Percolation.MaskChain','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
  for i in needed[off:off+40]:
   clause,body=proofs[i];assert re.sub(r'\s','',clause)=='['+','.join(f'({abs(x)-1},{str(x<0).lower()})' for x in db[i])+']'
   body=body.replace(f'cl_{i}',f'inputClause{i}');a,b=mask(db[i]);out += [f'def inputClause{i} : CNF.NClause := {clause}',f'theorem inputList{i} (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause{i} := by','  '+body.replace('\n','\n  '),f'mask_input "{i}|{a}|{b}"']
  (s/f'{name}.lean').write_text('\n'.join(out+['end Percolation.MaskChain'])+'\n')
 used.update(needed);newmods+=imods
 starts=[]
 cursor=lo
 while cursor<hi:
  stop=cursor;hintcount=0
  while stop<hi and stop-cursor<(100 if lo<18561 else 500):
   nh=len(steps[stop][2])
   if stop>cursor and hintcount+nh>25000 and lo>=18561:break
   hintcount+=nh;stop+=1
  starts.append((cursor,stop));cursor=stop
 for start,end in starts:
  name=f'R8Chain{start:06d}';imports=[previous]+(imods if start==lo else []);rows=[]
  for i,c,hs in steps[start:end]:
   f=set(c);parts=[]
   for hid in hs:
    rem=[x for x in db[hid] if x not in f];a,b=mask(db[hid])
    if not rem:parts.append(f'{hid},{a},{b},x,0')
    else:
     assert len(rem)==1,(i,hid);u=rem[0];f.add(-u);parts.append(f'{hid},{a},{b},{abs(u)-1},{int(u<0)}')
   a,b=mask(c);rows.append(f'{i}|{a}|{b}|'+ ';'.join(parts))
  (s/f'{name}.lean').write_text('\n'.join('import '+x for x in imports)+'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nmask_chain '+json.dumps('\n'.join(rows))+'\n');previous=name;newmods.append(name);meta[name]={'start':start,'end':end,'hints':sum(len(x[2]) for x in steps[start:end])}
  chain.append(name)
 meta[str(lo)]={'new_inputs':len(needed),'input_modules':imods,'end':hi,'hints':sum(len(x[2]) for x in steps[lo:hi])}
(p/'module-order.txt').write_text('\n'.join(original+newmods)+'\n')
(r/'generation.json').write_text(json.dumps(meta,indent=2))
# Fresh extraction is the only compilation tree.
for f in s.glob('*.lean'):
 dst=r/'fresh-extracted/src'/f.name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dst)
(r/'fresh-extracted/module-order.txt').write_text((p/'module-order.txt').read_text())
(r/'progress.json').write_text(json.dumps({'completed_modules':0,'closed_additions':0,'inherited_frontier':5000,'status':'fresh replay pending'}))
