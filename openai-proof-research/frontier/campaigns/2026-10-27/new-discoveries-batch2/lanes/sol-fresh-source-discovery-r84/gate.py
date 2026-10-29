from pathlib import Path
import json,re,hashlib,datetime
P=Path(__file__).resolve().parent; root=P.parents[5]; batch=P.parents[1]
pat=re.compile(r'2410\.13920|Bernoulli structure|Fontana|Semeraro|2312\.01819|Tsallis.*heat|2111\.06997|varentropy',re.I)
files=[];hits=[]
for p in root.rglob('*'):
 if not p.is_file() or P in p.parents:continue
 n=p.name.lower()
 if p.suffix not in ['.md','.json','.txt']:continue
 if not any(s in n for s in ['findings','discovery','summary','provenance']):continue
 files.append(str(p))
 if p.stat().st_size>4000000:continue
 s=p.read_text(errors='replace');ms=list(pat.finditer(s))
 if ms:
  hits.append({'path':str(p),'matches':len(ms),'sections':[s[max(0,m.start()-220):m.end()+450] for m in ms[:3]]})
(P/'all-date-report-filenames.txt').write_text('\n'.join(files)+'\n')
(P/'duplicate-filenames.txt').write_text('\n'.join(x['path'] for x in hits)+'\n')
(P/'duplicate-sections.json').write_text(json.dumps(hits,indent=2))
context={}
for n in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:
 p=batch/n;s=p.read_bytes();o={'sha256':hashlib.sha256(s).hexdigest(),'bytes':len(s)}
 if n.endswith('.json'):
  j=json.loads(s);o['keys']=list(j)
  if n=='ledger.json':o['counts']={k:j[k] for k in ['accepted_count','previous_accepted_count','total_accepted_count']};o['accepted_titles']=[x['title'] for x in j['accepted']]
  else:o['content']=j
 context[n]=o
(P/'context.json').write_text(json.dumps(context,indent=2))
reg=batch/'lanes/root-edge-irregulator-final-freeze-r1'; terms=re.compile('fontana|semeraro|bernoulli.*structure|tsallis|renyi.*monot|lyapunov|varentropy',re.I)
out={}
for n in ['omega','openai']:
 p=reg/(n+'-tree.txt');matches=[];count=0
 with p.open() as f:
  for line in f:
   count+=1
   if terms.search(line):matches.append(line.strip())
 out[n]={'lines':count,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'matches':matches}
(P/'registry-screen.json').write_text(json.dumps(out,indent=2))
print(json.dumps({'reports':len(files),'hits':len(hits),'registries':out},indent=2))
