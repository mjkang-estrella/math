import pathlib,json
r=pathlib.Path(__file__).resolve().parent
d=json.loads((r/'normalized-trimmed.json').read_text())
db={}
for l in (r/'normalized.cnf').read_text().splitlines():
 if l and l[0] not in 'cp': db[len(db)+1]=list(map(int,l.split()))[:-1]
db.update({s[0]:s[1] for s in d['steps']})
def mask(c):
 p=n=0
 for x in c:
  if x>0:p|=1<<(abs(x)-1)
  else:n|=1<<(abs(x)-1)
 return f'({p},{n})'
rows=[]
for start in range(13561,18561,100):
 name=f'MaskPilot{start-13561:04d}'
 out=['import MaskRUP','namespace Percolation.MaskRUP','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
 hints=0
 for idx in range(start,start+100):
  cid,c,hs=d['steps'][idx]; f=set(c); hh=[]
  for hid in hs:
   rem=[x for x in db[hid] if x not in f]
   if not rem: u=None
   else:
    assert len(rem)==1,(idx,hid,rem)
    u=rem[0];f.add(-u)
   hh.append(f'({mask(db[hid])},'+('none)' if u is None else f'some ({abs(u)-1},{str(u<0).lower()}))'))
  hints+=len(hh)
  out += [f'def c{idx} : Mask := {mask(c)}',f'def hs{idx} : List Hint := ['+','.join(hh)+']',f'theorem ck{idx} : check c{idx} hs{idx} = true := by decide',f'theorem sound{idx} (v : Nat → Bool) (hh : ∀ h ∈ hs{idx}, Holds v h.1) : Holds v c{idx} := check_sound c{idx} hs{idx} ck{idx} v hh']
 out+=['end Percolation.MaskRUP']
 (r/'packet/src'/f'{name}.lean').write_text('\n'.join(out)+'\n')
 rows.append({'module':name,'start':start,'end':start+100,'hint_uses':hints})
(r/'pilot-info.json').write_text(json.dumps(rows,indent=2))
