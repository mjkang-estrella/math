from pathlib import Path
import json,os,fnmatch,re,hashlib
r=Path(__file__).parent;p=r/'packet/private';g=json.loads((r/'guards.json').read_text())
def blocked(s):
 s=s.casefold();return s==g['own_root'].casefold() or any(x in s for x in g['substrings']) or any(fnmatch.fnmatchcase(s,x) for x in g['wildcards'])
terms=re.compile(r'complement|cartier|fano|log.discrepanc|log.canonical.threshold|bounded.index|base.locali[sz]|finite.rational|coefficient.set',re.I)
hits=[];eligible=0;nonutf=0
for base,ds,fs in os.walk('.',topdown=True,followlinks=False):
 ds[:]=sorted(d for d in ds if not blocked((Path(base)/d).as_posix()) and not (Path(base)/d).is_symlink())
 for name in sorted(fs):
  f=Path(base)/name;s=f.as_posix()
  if blocked(s) or f.is_symlink() or not any(t in s.casefold().split('/') for t in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']):continue
  b=f.read_bytes()
  try:t=b.decode('utf-8')
  except UnicodeDecodeError:nonutf+=1;continue
  eligible+=1;ms=list(terms.finditer(t))
  if ms:
   hs=[]
   for match in ms[:12]:
    a=t.rfind('\n',0,match.start())+1;e=t.find('\n',match.end());e=len(t) if e<0 else e;hs.append({'byte':len(t[:a].encode()),'line':t[a:e][:350]})
   hits.append({'path':s,'count':len(ms),'snippets':hs})
(p/'navigation.json').write_text(json.dumps({'eligible':eligible,'nonutf':nonutf,'hits':hits},indent=2)+'\n')
print(json.dumps({'eligible':eligible,'nonutf':nonutf,'hits':[{k:v for k,v in h.items() if k!='snippets'} for h in hits]},indent=2))
