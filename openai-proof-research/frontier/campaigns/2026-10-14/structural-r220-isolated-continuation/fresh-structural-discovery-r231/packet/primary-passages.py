from pathlib import Path
import sys,json,hashlib,datetime
R=Path(__file__).parent
for arg in sys.argv[1:]:
 name,span=arg.rsplit(':',1);lo,hi=map(int,span.split('-')); p=R/'private/primary'/(name+'.txt')
 data=p.read_bytes();ls=data.splitlines(keepends=True);assert 1<=lo<=hi<=len(ls)
 masks=json.loads((R/'private/primary/masks.json').read_text()).get(name,[])
 a=sum(map(len,ls[:lo-1]));b=sum(map(len,ls[:hi])); selected=[];out=[]
 off=a
 for i in range(lo,hi+1):
  line=ls[i-1]
  if any(x<=i<=y for x,y in masks):out.append('[MASKED classified nonmathematical line '+str(i)+']\n')
  else:out.append(line.decode());selected.append([off,off+len(line)])
  off+=len(line)
 entry={'file':str(p.relative_to(R)),'start':a,'end':b,'lines':[lo,hi],'selected_ranges':selected,'sha256_unmasked_interval':hashlib.sha256(data[a:b]).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'bytes.splitlines UTF8 text; exact declared furniture masks; extraction symbols may require visual recovery'}
 with (R/'private/primary-reads.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
 print('\nPRIMARY '+name+' lines '+str(lo)+'-'+str(hi)+' bytes '+str(a)+'-'+str(b)+'\n'+''.join(out))
