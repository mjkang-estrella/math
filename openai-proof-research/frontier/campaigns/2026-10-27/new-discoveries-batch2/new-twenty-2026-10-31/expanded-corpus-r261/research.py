import resource,pathlib,json,hashlib,datetime,subprocess,urllib.request,time,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
P=pathlib.Path(__file__).resolve().parent; root=P.parents[4]; data=json.loads((P/'extracted.json').read_text()); sha=lambda b:hashlib.sha256(b).hexdigest()
mode=sys.argv[1]; receipts=[]; start=time.monotonic()
if mode=='history':
 for k,v in data.items():
  r=v['record']; patterns=[k,r['title'],r['source_url'].rsplit('/',1)[-1]]
  cmd=['rg','-l','-i','-F',*sum((['-e',x] for x in patterns),[]),'-g','*.md','-g','*.json','-g','*.txt','-g','*.yml','-g','!mathdb-normalized*','-g','!routing*','-g','!screening*','-g','!reservation.json','-g','!extracted.json','-g','!results.json','-g','!raw/**',str(root)]
  cp=subprocess.run(cmd,capture_output=True,timeout=45); (P/f'history-{k}.txt').write_bytes(cp.stdout)
  receipts.append({'id':k,'command':cmd,'exit':cp.returncode,'sha256':sha(cp.stdout),'files':len(cp.stdout.splitlines())})
elif mode=='fetch':
 (P/'sources').mkdir(exist_ok=True)
 for spec in sys.argv[2:]:
  name,url=spec.split('=',1); dest=P/'sources'/name; rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':str(dest)}
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research (public source review)'}),timeout=18) as resp:
    b=resp.read(20*1024**2+1); assert len(b)<=20*1024**2; rec.update(status=resp.status,final_url=resp.url,sha256=sha(b),bytes=len(b)); dest.write_bytes(b)
  except Exception as e: rec.update(error=str(e))
  receipts.append(rec); print(json.dumps(rec),flush=True)
  if time.monotonic()-start>115: break
path=P/f'{mode}-receipts.jsonl'
with path.open('a') as f:
 for r in receipts:f.write(json.dumps(r)+'\n')
print('Completed',mode,'seconds',time.monotonic()-start)
