import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import runpy,sys,json,base64,re
D=runpy.run_path(__file__.replace('inspect.py','audit.py'));read=D['read'];A=D['A'];write=D['write'];items=D['items']
mode=sys.argv[1]
if mode=='meta':
 for name in ['provenance.json','results.json']:
  j=json.loads(read(A/name)); print(name,json.dumps(j['335255'],indent=2))
 print('BRIEF REMAINDER',read(A/'BRIEF.md').split('## Other exact results and precise holds')[1])
 for p in json.loads(read(D['L']/'frozen-inputs.json')):
  if '/receipts/' in p:
   j=json.loads(read(p));
   for h in j.get('http',[]):print(json.dumps(h))
elif mode=='history':
 allow=json.loads(read(A/'historical-results-allowlist.json'));n=0;matches=[]
 for p in allow:
  if any(x in p.lower() for x in ['crown','transitive-bunkbed','tournament','protected']):continue
  s=read(p);n+=1
  for q in ['335255','product of difference sets','14078','1702.02544','square.zero']:
   for m in re.finditer(q,s,re.I):matches.append({'path':p,'query':q,'window':s[max(0,m.start()-200):m.end()+300]})
 print('HISTORY',n,json.dumps(matches));write('history-review.json',json.dumps({'opened':n,'matches':matches,'filter_before_open':True},indent=2))
elif mode=='registry':
 for name in sys.argv[2:]:
  s=base64.b64decode(read(A/('sources/'+name+'.b64'))).decode(errors='replace');print('REGISTRY',name,'bytes',len(s));
  if 'head' in name or len(s)<3000: print(s)
  else:
   for line in s.splitlines():
    if re.search('ring|difference|Fish|335255|CONTENT|github|catalog',line,re.I):print(line[:1500])
write('receipts/inspect-'+D['stamp']+'.json',json.dumps(items,indent=2))
