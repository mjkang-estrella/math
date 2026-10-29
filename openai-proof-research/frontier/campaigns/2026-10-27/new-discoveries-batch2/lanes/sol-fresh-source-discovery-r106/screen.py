from pathlib import Path
import hashlib,json,re,subprocess,datetime
P=Path(__file__).resolve().parent;root=Path('openai-proof-research').resolve()
terms={'cosine_minima':r'2605\.02023|Kunisky|Litvak|volumetric.{0,30}zone|cosine.{0,40}(minim|config)', 'simplex':r'2607\.14087|2608\.19093|2609\.28452|simplex.{0,25}(width|Gaussian|measure)|Mulgund', 'transport':r'2607\.23241|Dacorogna|Conforti.{0,35}Lacker|geodesic.{0,30}coupling'}
assert re.search(terms['cosine_minima'],'2605.02023')
patterns={k:re.compile(v,re.I) for k,v in terms.items()};hits={k:[] for k in terms};count=0;errors=[]
with (P/'duplicate-corpus.jsonl').open('w') as out:
 for name in subprocess.Popen(['rg','--files','--hidden',str(root)],stdout=subprocess.PIPE,text=True).stdout:
  f=Path(name.rstrip('\n'))
  if P in f.parents or f.suffix.lower() not in ['.md','.txt','.json','.tex','.jsonl']:continue
  if not(any(t in f.name.lower() for t in ['summary','discovery','findings','proof','review','ledger']) or 'review' in str(f).lower()):continue
  try:
   h=hashlib.sha256();found=set();tail=b''
   with f.open('rb') as src:
    while True:
     b=src.read(65536)
     if not b:break
     h.update(b);s=(tail+b).decode(errors='replace')
     for k,p in patterns.items():
      if k not in found and p.search(s):found.add(k)
     tail=b[-512:]
   rel=str(f.relative_to(root));out.write(json.dumps([rel,h.hexdigest()])+'\n');count+=1
   for k in found:hits[k].append(rel)
  except Exception as e:errors.append([str(f),repr(e)])
(P/'duplicate-audit.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'ALL dates, SUMMARY/discovery/FINDINGS/PROOF/review/ledger filename and review-directory text; streaming hash and chunk matching; no corpus cap','files':count,'patterns':terms,'literal_id_selfcheck':True,'hits':hits,'errors':errors},indent=2));print(count,{k:len(v) for k,v in hits.items()},errors)
