exec(compile((__import__('pathlib').Path(__file__).resolve().parent/'research.py').read_text(),'research.py','exec'))
import re
out={}
for row in r['rows']:
 k=str(row['mathdb_id']);s=(L/'sources'/(k+'.txt')).read_text(); lines=s.splitlines(); ranges=[]
 for i,line in enumerate(lines):
  if re.search(r'conjecture',line,re.I):ranges.append((max(0,i-3),min(len(lines),i+15)))
 if sys.argv[1]=='all':ranges=ranges[:5]
 elif k not in sys.argv[2:]:continue
 # bounded selections, not full-body claim
 blocks=[dict(start_line=a+1,end_line=b,text='\n'.join(lines[a:b])) for a,b in ranges]
 out[k]=blocks;print('\nID',k,'TOTAL LINES',len(lines));print('\n'.join(f"LINES {x['start_line']}-{x['end_line']}\n{x['text']}" for x in blocks))
js('reads/'+sys.argv[1]+'-excerpts.json',out);receipt('read-'+sys.argv[1],dict(ids=list(out),scope='printed exact excerpts only'))
