from pathlib import Path
import urllib.request,urllib.error,hashlib,json,subprocess
L=Path(__file__).resolve().parent
targets={'1912.12545':['schinzel','zassenhaus','dimitrov'],'1907.04593':['duffin','schaeffer','koukoulopoulos'],'2101.04698':['faber','lovász','lovasz','kang kelly'],'2303.10798':['einstein','aperiodic monotile','smith myers']}
rows=[];dedup=[]
for p in sorted(L.parent.glob('*/SCOUTING.md')):
 if p.parent==L:continue
 data=p.read_bytes();text=data.decode(errors='replace').lower();h=hashlib.sha256(data).hexdigest()
 hits={k:[x for x in words if x in text] for k,words in targets.items()};hits={k:v for k,v in hits.items() if v}
 if hits:dedup.append(dict(path=str(p),sha256=h,hits=hits))
(L/'dedup.json').write_text(json.dumps(dedup,indent=2)+'\n')
(L/'sources').mkdir(exist_ok=True)
for id in targets:
 url='https://arxiv.org/pdf/'+id
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=25) as r:
   data=r.read(12*1024*1024);status=r.status
  if not data.startswith(b'%PDF'):raise RuntimeError('non-PDF/challenge; stop')
  p=L/'sources'/(id+'.pdf');p.write_bytes(data)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=25)
  rows.append(dict(url=url,status=status,pdf_sha256=hashlib.sha256(data).hexdigest(),text_sha256=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()))
 except Exception as e:
  rows.append(dict(url=url,error=str(e),policy='no retry or bypass'))
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):break
  if 'challenge' in str(e):break
(L/'access.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows))
