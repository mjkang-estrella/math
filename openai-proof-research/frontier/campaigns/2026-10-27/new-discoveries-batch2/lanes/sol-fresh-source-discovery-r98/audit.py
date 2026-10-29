from pathlib import Path
import re,json,hashlib,subprocess
P=Path(__file__).resolve().parent; root=Path('openai-proof-research').resolve()
terms={'ikl':r'2504\.17567|inverse.{0,12}Kazhdan|Xie.{0,20}Zhang','git':r'2505\.01087|Choi.{0,15}Kiem|GIT.{0,35}(log.concav|characteristic)|Conjecture.?4\.10','fayers_retired':r'2508\.00074|Fayers'}
proc=subprocess.Popen(['rg','--files','--hidden',str(root)],stdout=subprocess.PIPE,text=True)
def selected_files():
 for line in proc.stdout:
  f=Path(line.strip())
  if (any(x in f.name.lower() for x in ['summary','discovery','findings','proof','review','ledger']) or ('review' in str(f).lower() and f.suffix.lower()=='.md')) and P not in f.parents and f.suffix.lower() in ['.md','.json','.txt','.tex']:
   yield f
selected=selected_files()
seen={};hits={k:[] for k in terms}; manifest=[]; count=0
for f in selected:
 count+=1
 b=f.read_bytes(); h=hashlib.sha256(b).hexdigest();manifest.append([str(f.relative_to(root)),h])
 if h in seen:continue
 seen[h]=str(f.relative_to(root));s=b.decode(errors='replace')
 for k,t in terms.items():
  ls=[{'line':i,'text':l[:900]} for i,l in enumerate(s.splitlines(),1) if re.search(t,l,re.I)]
  if ls:hits[k].append({'path':str(f.relative_to(root)),'sha256':h,'hits':ls})
(P/'duplicate-corpus.json').write_text(json.dumps(manifest));(P/'duplicate-audit.json').write_text(json.dumps({'files':count,'unique_contents':len(seen),'scope':'ALL dates under research root; filename contains summary/discovery/findings/proof/review/ledger; text md/json/txt/tex; no file/date cap','hits':hits},indent=2))
print(count,len(seen));print({k:len(v) for k,v in hits.items()})
