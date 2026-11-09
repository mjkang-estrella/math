import runpy,sys,json
from pathlib import Path
r=Path(__file__).resolve().parent;ns=runpy.run_path(str(r/'read_selected.py'));plan=json.loads((r/'private/primary-selections.json').read_bytes());name=sys.argv[1];path=f'private/primary/{name}.txt';b,ll,oo=ns['data'](path);ranges=plan['ranges'][name]
if len(sys.argv)>2:ranges=[ranges[int(sys.argv[2])]]
for start,end in ranges:
 print('MATHEMATICAL READ',path,'L',start,end,'bytes',oo[start-1],oo[end])
 for i in range(start-1,end):
  if i+1 in plan['exclude_lines'][name]:print(f'[Excluded nonmathematical running header/editorial line {i+1}]')
  else:print(f'{i+1:4d} '+ll[i].decode(),end='')
 with (r/'private/read-selections.jsonl').open('a') as h:h.write(json.dumps({'path':path,'lines_inclusive':[start,end],'bytes_half_open':[oo[start-1],oo[end]],'exclude_lines':plan['exclude_lines'][name]})+'\n')
