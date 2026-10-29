import os,re,json,hashlib,gzip,sqlite3,sys,urllib.request,datetime
from pathlib import Path
H=Path(__file__).resolve().parent
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
def save(n,x): (H/n).write_text(json.dumps(x,indent=2)+'\n')
def fetch(url,n):
 d={'url':url,'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':n}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-research/1.0'}),timeout=30) as f:
   b=f.read(12000001);assert len(b)<=12000000; (H/n).write_bytes(b);d.update(status=f.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),final_url=f.url)
 except Exception as e:d['error']=str(e)
 with (H/'http.jsonl').open('a') as f:f.write(json.dumps(d)+'\n')
 print(json.dumps(d))
patterns={
'domino-id':r'2501[.]17765','domino-title':r'Domino\s+Tilings.{0,20}Domino\s+Shuffling|rank.determined.{0,30}linear.factors','domino-authors':r'Cavey|Yi.Lin\s+Lee','domino-statement':r'divisib.{0,100}(?:rank|nabla)|(?:rank|nabla).{0,100}divisib',
'partite-id':r'2410[.]11194','partite-title':r'Partite\s+saturation\s+number\s+of\s+cycles','partite-authors':r'Yiduo\s+Xu|Zhen\s+He.{0,60}Mei\s+Lu','partite-statement':r'(?:bipartite|partite).{0,80}(?:even.cycle|saturat)|sat\s*\(.{0,30}C_?\{?2',
'spectral-title':r'minimum\s+spectral\s+radius.{0,80}saturat|spectral\s+saturation','spectral-authors':r'Kim.{0,25}Kim.{0,25}Kostochka|Suil\s+O','spectral-statement':r'sat_?(?:rho|ρ)|saturat.{0,80}spectral|spectral.{0,80}saturat'}
def screen():
 db=sqlite3.connect(H/'screen.sqlite');db.execute('create table bodies(hash text primary key, path text)')
 pats=[(k,re.compile(v,re.I)) for k,v in patterns.items()]
 st={'scope':str(R),'all_dates':True,'global_hit_cutoff':None,'text_limit_bytes':12000000,'per_match_excerpt_chars':400,'per_file_match_limit':None,'paths':0,'unique':0,'duplicates':0,'excluded_roles':{},'omitted_extensions':{},'oversized':[],'errors':[],'binary':0,'required_r111_r113':[]}
 exts={'.md','.txt','.json','.jsonl','.py','.lean','.tex','.html','.htm','.csv','.tsv','.yaml','.yml','.rst','.log','.sh'}
 with gzip.open(H/'pathmap.jsonl.gz','wt') as mp,(H/'matches.jsonl').open('w') as out:
  for base,dirs,files in os.walk(R):
   dirs[:]=[d for d in dirs if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=H]
   for fn in files:
    p=Path(base,fn);rel=str(p.relative_to(R));ext=p.suffix.lower()
    if ext not in exts:st['omitted_extensions'][ext]=st['omitted_extensions'].get(ext,0)+1;continue
    role=re.search(r'(?:pathmap|path-map|hash-path|screen-hits|screen-matches|target-matches|focused-hits|refined-matches|history-matches|inventory|preprints-tree|tree-cache|search-receipts)',fn,re.I)
    if role:st['excluded_roles'][role[0]]=st['excluded_roles'].get(role[0],0)+1;continue
    try:
     if p.stat().st_size>12000000:st['oversized'].append(rel);continue
     b=p.read_bytes();st['paths']+=1
     if b'\0' in b:st['binary']+=1;continue
     h=hashlib.sha256(b).hexdigest();mp.write(json.dumps({'path':rel,'sha256':h})+'\n')
     if re.search(r'r11[123]/',rel) and re.search(r'SUMMARY|discovery|PROOF|review',fn,re.I):st['required_r111_r113'].append(rel)
     try:db.execute('insert into bodies values(?,?)',(h,rel))
     except sqlite3.IntegrityError:st['duplicates']+=1;continue
     st['unique']+=1
     continue # Hash corpus only. Uncapped native-rg target matching is a separate pass.
     low=b.lower()
     if not any(t in low for t in [b'2501.17765',b'2410.11194',b'domino',b'cavey',b'lee',b'divisib',b'saturat',b'yiduo',b'zhen',b'kim',b'suil',b'sat_',b'sat(',b'sat (']):continue
     s=b.decode('utf-8','replace')
     for key,pat in pats:
      triggers={'domino-id':[b'2501.17765'],'domino-title':[b'domino',b'rank'],'domino-authors':[b'cavey',b'lee'],'domino-statement':[b'divisib'],'partite-id':[b'2410.11194'],'partite-title':[b'saturation'],'partite-authors':[b'xu',b'zhen'],'partite-statement':[b'sat',b'partite'],'spectral-title':[b'spectral'],'spectral-authors':[b'kim',b'suil'],'spectral-statement':[b'sat']}
      if not any(t in low for t in triggers[key]):continue
      for m in pat.finditer(s):out.write(json.dumps({'key':key,'path':rel,'sha256':h,'offset':m.start(),'excerpt':s[max(0,m.start()-180):m.end()+220]})+'\n')
    except Exception as e:st['errors'].append({'path':rel,'error':str(e)})
 db.commit();save('screen-receipt.json',st);print(json.dumps(st))
def context():
 batch=H.parent.parent;receipts=[]
 for name in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  p=batch/name;b=p.read_bytes();receipts.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
  if name.endswith('.json'):
   x=json.loads(b); print(name, json.dumps(x)[:3000]);
  else:
   # Context is mutable coordination, separate from scientific freeze.
   (H/'NEXT-as-read.md').write_bytes(b); print('NEXT tail',b.decode()[-12000:])
 save('context-receipts.json',receipts)
if __name__=='__main__':
 if sys.argv[1]=='screen':screen()
 elif sys.argv[1]=='fetch':fetch(sys.argv[2],sys.argv[3])
 elif sys.argv[1]=='context':context()
