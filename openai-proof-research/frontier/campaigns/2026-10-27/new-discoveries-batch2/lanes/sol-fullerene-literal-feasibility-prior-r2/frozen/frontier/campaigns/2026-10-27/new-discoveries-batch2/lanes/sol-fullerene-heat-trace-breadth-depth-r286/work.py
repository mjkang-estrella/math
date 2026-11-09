from pathlib import Path
import sys,hashlib,json,datetime,urllib.request,subprocess,re
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(p,original=None,url=None):
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(dict(path=str(p.relative_to(L)),original=str(original) if original else None,url=url,sha256=sha(p),bytes=p.stat().st_size,time=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
def freeze(p):
 p=Path(p).resolve(); q=L/'frozen'/('ref-'+hashlib.sha256(str(p).encode()).hexdigest()[:12]+'-'+p.name)
 if not q.exists():
  h=sha(p);q.write_bytes(p.read_bytes());assert h==sha(q)==sha(p);bind(q,p)
 return q
cmd=sys.argv[1]
if cmd=='freeze':
 for p in sys.argv[2:]: print(freeze(p))
elif cmd=='read':
 p=freeze(sys.argv[2]);s=p.read_text(errors='replace'); pat=sys.argv[3] if len(sys.argv)>3 else '.'
 lines=s.splitlines();hits=[i for i,x in enumerate(lines) if re.search(pat,x,re.I)]
 for i in hits[:int(sys.argv[4]) if len(sys.argv)>4 else 30]:print('\n'.join(f'{j+1}: {lines[j]}' for j in range(max(0,i-5),min(len(lines),i+13))))
 assert sha(Path(sys.argv[2]))==sha(p)
elif cmd=='fetch':
 name,url=sys.argv[2:4];p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Research source verification (bounded request)'})
  with urllib.request.urlopen(req,timeout=25) as r:
   data=r.read(15000000);status=r.status
  p.write_bytes(data);bind(p,url=url);print(name,status,len(data))
  if data.startswith(b'%PDF'):
   q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);bind(q,original=p,url='derived:'+url)
 except Exception as e:
  with (L/'failures.jsonl').open('a') as f:f.write(json.dumps(dict(url=url,error=str(e),time=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
  print('FAIL',url,str(e))
elif cmd=='scan':
 base=Path(sys.argv[2]);pat=re.compile(sys.argv[3],re.I);out=[]
 for p in base.rglob('*'):
  if p.is_file() and p.suffix in ['.md','.json','.lean','.txt'] and p.stat().st_size<3000000:
   # Freeze matching bodies before scientific consumption; raw matching is navigation only.
   if pat.search(p.read_text(errors='replace')):out.append(str(p))
 (L/'scan-paths.json').write_text(json.dumps(out[:500],indent=2));print('\n'.join(out[:120]))
