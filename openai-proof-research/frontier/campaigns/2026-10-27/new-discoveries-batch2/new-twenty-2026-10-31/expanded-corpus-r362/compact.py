exec(compile((__import__('pathlib').Path(__file__).resolve().parent/'research.py').read_text(),'research.py','exec'))
import re
keys=sys.argv[1:] or [str(x) for x in r['ids']]
outs={}
for k in keys:
 s=(L/'sources'/(k+'.txt')).read_text().splitlines();inds=[i for i,t in enumerate(s) if re.search(r'^\s*(Conjecture|CONJECTURE)\s',t)]
 # human will read selected statements, not every matching hit
 out=[]
 for i in inds[-3:]:
  a=max(0,i-2);b=min(len(s),i+16);out.append(dict(start_line=a+1,end_line=b,text='\n'.join(s[a:b])))
 if not out:out=[dict(start_line=1,end_line=min(30,len(s)),text='\n'.join(s[:30]))]
 outs[k]=out;print('\nID',k);print('\n'.join(f"LINES {x['start_line']}-{x['end_line']}\n{x['text']}" for x in out))
js('reads/compact-'+keys[0]+'.json',outs);receipt('compact-'+keys[0],dict(ids=keys))
