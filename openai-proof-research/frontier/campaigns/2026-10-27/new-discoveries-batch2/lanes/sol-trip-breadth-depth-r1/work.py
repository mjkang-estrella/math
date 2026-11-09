from pathlib import Path
import hashlib,json,sys,shutil,datetime,urllib.request,subprocess
L=Path(__file__).resolve().parent; B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze():
 out=[]
 files=[B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']
 R=L.parent/'sol-wide-new-mechanism-scout-r220'
 files += [R/n for n in ['SCOUTING.md','SUMMARY.md','discovery.md','FAILURES.md','provenance.json','frozen/history-index.json','sources/2410.02032v2.pdf','sources/2410.02032v2.txt']]
 for p in files:
  if not p.exists(): continue
  admin=p.parent==B or p.name=='AGENTS.md'
  dst=L/('administrative' if admin else 'frozen')/("batch-AGENTS.md" if p==B/"AGENTS.md" else p.name);dst.parent.mkdir(parents=True,exist_ok=True)
  a=sha(p);shutil.copyfile(p,dst);assert a==sha(p)==sha(dst)
  out.append(dict(original=str(p),copy=str(dst.relative_to(L)),sha256=a,administrative=admin))
 (L/'freeze.json').write_text(json.dumps(out,indent=2))
def fetch(url,name):
 p=L/'sources'/name;p.parent.mkdir(exist_ok=True)
 rec=dict(url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=35) as r:
   data=r.read(16000000);rec.update(status=r.status,final_url=r.url,size=len(data))
  p.write_bytes(data);rec['sha256']=sha(p)
 except Exception as e:rec['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec))
def bodies():
 for ident in ['2412.09227v3','2412.05750v2','2411.17145v1','2412.15457v2','2412.04288v1','2412.19593v1','2412.21128v2','2412.04420v1','2412.20120v2']:
  fetch('https://arxiv.org/pdf/'+ident,ident+'.pdf')
  p=L/'sources'/(ident+'.pdf')
  if p.exists():
   h=sha(p);subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True);assert sha(p)==h
def history():
 idx=json.loads((L/'frozen/history-index.json').read_text());records=[];hits=[]
 terms=['2412.09227','2412.05750','2411.17145','2412.15457','2412.04288','2412.19593','2412.21128','2412.04420','2412.20120','Levenshtein','Buratti','arborescence','weak order','Brenti','Negami','Gamma-Theta','A-period']
 for r in idx['records']:
  p=Path(r['snapshot_reference']);assert sha(p)==r['sha256'];s=p.read_text(errors='replace')
  matches=[t for t in terms if t.lower() in s.lower()]
  if matches:hits.append(dict(path=str(p),terms=matches))
  records.append(dict(path=str(p),sha256=r['sha256']))
 # Newest scout reports not already frozen by r220 history.
 for p in sorted(L.parent.glob('sol-*r21[3-9]/SCOUTING.md'))+sorted(L.parent.glob('sol-*r22[01]/SCOUTING.md')):
  h=sha(p);s=p.read_text();assert h==sha(p);records.append(dict(path=str(p),sha256=h))
  matches=[t for t in terms if t.lower() in s.lower()]
  if matches:hits.append(dict(path=str(p),terms=matches))
 (L/'history-bindings.json').write_text(json.dumps(records,indent=2));(L/'history-hits.json').write_text(json.dumps(hits,indent=2));print('verified',len(records),'hits',len(hits))
if __name__=='__main__':
 if sys.argv[1]=='freeze':freeze()
 elif sys.argv[1]=='fetch':fetch(*sys.argv[2:])
 elif sys.argv[1]=='bodies':bodies()
 elif sys.argv[1]=='history':history()
