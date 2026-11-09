import pathlib,json
r=pathlib.Path(__file__).resolve().parent;d=json.loads((r/'normalized-trimmed.json').read_text());db={}
for l in (r/'normalized.cnf').read_text().splitlines():
 if l and l[0] not in 'cp':db[len(db)+1]=list(map(int,l.split()))[:-1]
db.update({i:c for i,c,h in d['steps']})
def mask(c):
 p=n=0
 for x in c:
  if x>0:p|=1<<(x-1)
  else:n|=1<<(-x-1)
 return p,n
for start in range(13561,18561,100):
 rows=[]
 for idx in range(start,start+100):
  i,c,hs=d['steps'][idx];f=set(c);parts=[]
  for hid in hs:
   rem=[x for x in db[hid] if x not in f];a,b=mask(db[hid])
   if not rem:parts.append(f'{a},{b},x,0')
   else:
    assert len(rem)==1
    u=rem[0];f.add(-u);parts.append(f'{a},{b},{abs(u)-1},{int(u<0)}')
  a,b=mask(c);rows.append(f'{idx}|{a}|{b}|'+ ';'.join(parts))
 text='import MaskBuild\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nmask_data '+json.dumps('\n'.join(rows))+'\n'
 (r/'packet/src'/f'MaskRaw{start-13561:04d}.lean').write_text(text)
