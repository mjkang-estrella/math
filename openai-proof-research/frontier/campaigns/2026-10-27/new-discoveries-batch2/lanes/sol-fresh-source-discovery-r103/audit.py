from pathlib import Path
import re,json,hashlib,subprocess
P=Path(__file__).resolve().parent;root=Path('openai-proof-research').resolve()
terms={'BNT_entropy_concavity':r'Ball.{0,25}Nayar.{0,25}Tkocz|entropy.{0,60}(weighted.*sum|concav.*sqrt)|2308\.15997|reverse entropy power', 'Feige_logconcave':r'Marsiglietti|Pandey|Feige.{0,40}log.concav', 'covariogram':r'covariogram|Matheron|Godbersen'}
files=subprocess.Popen(['rg','--files','--hidden',str(root)],stdout=subprocess.PIPE,text=True).stdout;manifest=[];hits={k:[] for k in terms};seen=set()
for name in files:
 f=Path(name.strip())
 if P in f.parents or f.suffix.lower() not in ['.md','.json','.txt','.tex']:continue
 if not (any(x in f.name.lower() for x in ['summary','discovery','findings','proof','review','ledger']) or 'review' in str(f).lower()):continue
 b=f.read_bytes();h=hashlib.sha256(b).hexdigest();manifest.append([str(f.relative_to(root)),h])
 if h in seen:continue
 seen.add(h)
 for k,t in terms.items():
  ls=[{'line':i,'text':s[:1200]} for i,s in enumerate(b.decode(errors='replace').splitlines(),1) if re.search(t,s,re.I)]
  if ls:hits[k].append({'path':str(f.relative_to(root)),'hits':ls})
(P/'duplicate-corpus.json').write_text(json.dumps(manifest));(P/'duplicate-audit.json').write_text(json.dumps({'scope':'ALL dates; all filename SUMMARY/discovery/FINDINGS/PROOF/review/ledger and review directories; md/json/txt/tex; no cap; identical byte bodies deduplicated','files':len(manifest),'unique_bodies':len(seen),'terms':terms,'hits':hits},indent=2));print(len(manifest),{k:len(v) for k,v in hits.items()})
for k,v in hits.items():
 print(k)
 for h in v[:15]:print(h['path'],h['hits'][0]['text'][:240])
