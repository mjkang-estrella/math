import pathlib,json,subprocess,hashlib,datetime,urllib.request,urllib.error,resource,os
R=pathlib.Path(__file__).resolve().parent;resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); rec=json.loads((R/'records.json').read_text());
if __name__=='__main__':
 mode=__import__('sys').argv[1]
 if mode=='history':
  pats=[]
  for i,v in rec.items(): pats.extend(['-e',i,'-e',v['record']['title']])
  p=subprocess.run(['rg','--no-ignore','-F','-n','-i','--max-columns','1000','--max-columns-preview','--max-count','5','--glob','*.md','--glob','*results*.json','--glob','*review*.json','--glob','*ledger*.json','--glob','!reservation.json','--glob','!expanded-corpus-r52/**',*pats,str(R.parents[3])],capture_output=True,text=True,timeout=70)
  lines=[s for s in p.stdout.splitlines() if '/expanded-corpus-r52/' not in s]; (R/'history-search.txt').write_text('\n'.join(lines)+'\n');print('matches',len(lines),'exit',p.returncode,'stderr',p.stderr[:500])
 if mode=='fetch':
  (R/'sources').mkdir(exist_ok=True);receipts=[]
  urls=[('openai-head','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head','https://api.github.com/repos/teorth/omega/commits/HEAD')]+[(a,'https://arxiv.org/pdf/'+a) for a in ['2304.01979','2304.11602','2305.05130','2304.12193','2306.02761','2305.08688','2305.03878']]
  for name,url in urls:
   t=datetime.datetime.now(datetime.timezone.utc).isoformat()
   try:
    with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical research source verification'}),timeout=25) as f: data=f.read();status=f.status;headers=dict(f.headers)
   except urllib.error.HTTPError as e: data=e.read();status=e.code;headers=dict(e.headers)
   except Exception as e: receipts.append({'url':url,'utc':t,'error':str(e)});continue
   path=R/'sources'/(name+('.pdf' if data[:4]==b'%PDF' else '.json'));path.write_bytes(data);receipts.append({'url':url,'utc':t,'status':status,'sha256':hashlib.sha256(data).hexdigest(),'file':str(path),'headers':headers});print(name,status,len(data),flush=True)
   if data[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(path),str(path.with_suffix('.txt'))],timeout=20)
  (R/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
