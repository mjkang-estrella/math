import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import runpy,sys,json,re,base64
D=runpy.run_path(__file__.replace('focus.py','audit.py'));read=D['read'];write=D['write'];L=D['L'];items=D['items']
mode=sys.argv[1]
if mode=='range':
 p=sys.argv[2];s=read(L/p if p.startswith('fresh/') else D['A']/p);a,z=map(int,sys.argv[3:]);print('\n'.join(f'{i+1}: {x}' for i,x in enumerate(s.splitlines()) if a<=i+1<=z))
elif mode=='scan':
 for n in sys.argv[2:]:
  s=read(L/('fresh/'+n+'.txt'));lines=s.splitlines();print('FILE',n,'LINES',len(lines));inds=set()
  for i,x in enumerate(lines):
   if re.search(r'Theorem [0-9]|Proposition [0-9]|Conjecture|nilpot|square.zero|finite ring',x,re.I):inds.update(range(max(0,i-2),min(len(lines),i+15)))
  for i in sorted(inds):print(f'{i+1}: {lines[i]}')
elif mode=='trees':
 for n in ['pool-tree','tau-tree']:
  s=base64.b64decode(read(L/('fresh/'+n+'.b64'))).decode();paths=sorted(set(re.findall(r'"path":"([^"\n]+)"',s)));print(n,'PATHS',len(paths));print('\n'.join(p for p in paths if re.search('algebra|combin|ring|additive|sumproduct|difference|Fish|335255|basic',p,re.I)))
 s=base64.b64decode(read(L/'fresh/openai-contents.b64')).decode();print('OPENAI exact terms');
 for q in ['finite commutative ring','product of difference','Fish,','335255','square-zero ideal']:
  print(q,[s[max(0,m.start()-150):m.end()+250] for m in re.finditer(re.escape(q),s,re.I)])
write('receipts/focus-'+D['stamp']+'.json',json.dumps(items,indent=2))
