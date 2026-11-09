from pathlib import Path
import json,hashlib,urllib.request,datetime,subprocess,sys,re
L=Path(__file__).resolve().parent
def dump(n,v): (L/n).write_text(json.dumps(v,indent=2))
def sha(d): return hashlib.sha256(d).hexdigest()
def freeze(p):
 d=p.read_bytes(); h=sha(d); q=L/'science'/(h[:16]+'-'+p.name);q.parent.mkdir(exist_ok=True)
 if not q.exists():q.write_bytes(d);q.chmod(0o444)
 assert sha(p.read_bytes())==sha(q.read_bytes())==h
 a=json.loads((L/'freeze.json').read_text());a.append(dict(original=str(p),copy=str(q),sha256=h));dump('freeze.json',a)
 return q
def get(url,name):
 p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 a=json.loads((L/'access.json').read_text()) if (L/'access.json').exists() else []
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research bounded primary-source reader'}),timeout=25) as r:
   d=r.read(10000001);assert len(d)<=10000000;p.write_bytes(d);a.append(dict(url=url,path=str(p),sha256=sha(d),status=r.status,headers=dict(r.headers),time=datetime.datetime.now(datetime.timezone.utc).isoformat()))
  dump('access.json',a);return freeze(p)
 except Exception as e:
  a.append(dict(url=url,error=str(e),time=datetime.datetime.now(datetime.timezone.utc).isoformat()));dump('access.json',a);print('FAILED',url,str(e));return None
if __name__=='__main__':
 if sys.argv[1]=='get':
  q=get(sys.argv[2],sys.argv[3]);print(q)
  if q and q.suffix=='.pdf':
   out=L/'texts'/sys.argv[3].replace('.pdf','.txt');out.parent.mkdir(exist_ok=True);subprocess.run(['pdftotext','-layout',str(q),str(out)],check=True);freeze(out)
 elif sys.argv[1]=='history':
  r=L.parent/'sol-wide-analytic-source-mechanisms-r259/expanded-history.json';j=json.loads(r.read_text()); rows=j['verified_references']; hits=[]
  terms=sys.argv[2:]
  for row in rows:
   p=Path(row['path']);d=p.read_bytes();assert sha(d)==row['sha256'];s=d.decode(errors='replace')
   found=[t for t in terms if t.lower() in s.lower()]
   if found:hits.append(dict(**row,terms=found,excerpts=[s[max(0,m.start()-100):m.end()+180] for t in found for m in list(re.finditer(re.escape(t),s,re.I))[:3]]))
  dump('history-screen.json',dict(reference_index=str(r),reference_sha256=sha(r.read_bytes()),verified=len(rows),terms=terms,hits=hits));print(json.dumps(hits,indent=2)[:18000])
