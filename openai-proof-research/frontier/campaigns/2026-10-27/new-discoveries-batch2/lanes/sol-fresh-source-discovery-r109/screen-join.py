from pathlib import Path
import hashlib,json,re,subprocess,datetime
P=Path(__file__).resolve().parent; R=Path('openai-proof-research').resolve()
terms={'join':r'Fáry|Fary|Rédei|Redei|unbalanced.{0,30}join|2610\.06806|2608\.06470'}
assert re.search(terms['join'],'2610.06806')
pat={k:re.compile(v,re.I) for k,v in terms.items()};hits={k:[] for k in terms};errors=[];n=0
with (P/'join-corpus.jsonl').open('w') as out:
 for name in subprocess.Popen(['rg','--files','--hidden',str(R)],stdout=subprocess.PIPE,text=True).stdout:
  f=Path(name.rstrip());rel=str(f.relative_to(R)); low=rel.lower()
  if P in f.parents or f.suffix.lower() not in ['.md','.txt','.json','.jsonl','.tex','.py','.sh','.js','.ts']:continue
  if not (any(x in f.name.lower() for x in ['summary','discovery','findings','proof','review','ledger','screened-out','openproblem']) or any(x in low for x in ['/tools/','/scripts/','/agent/','/agents/','review'])):continue
  try:
   h=hashlib.sha256();found=set();tail=b''
   with f.open('rb') as s:
    while True:
     b=s.read(65536)
     if not b:break
     h.update(b);t=(tail+b).decode(errors='replace')
     for k,p in pat.items():
      if k not in found and p.search(t):found.add(k)
     tail=b[-1024:]
   out.write(json.dumps([rel,h.hexdigest()])+'\n');n+=1
   for k in found:hits[k].append(rel)
  except Exception as e:errors.append([rel,repr(e)])
(P/'join-audit.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':n,'scope':'all dates; required report names plus SCREENED-OUT, openproblem, tools/scripts/agent and entire review trees; streaming chunk hashes; no aggregate source buffer','patterns':terms,'literal_id_selfcheck':True,'hits':hits,'errors':errors},indent=2)); print(n,{k:len(v) for k,v in hits.items()},errors)
