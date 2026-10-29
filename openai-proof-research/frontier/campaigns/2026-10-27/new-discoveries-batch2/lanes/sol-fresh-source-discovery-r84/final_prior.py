from pathlib import Path
import urllib.request,json,hashlib,datetime,re
P=Path(__file__).resolve().parent
head=json.loads((P/'sources/omega-head').read_text())['sha'];url='https://api.github.com/repos/the-omega-institute/trureturing/compare/e50b06adbf73bc8eaa5ae905ad0d7b0d178fe377...'+head
log=json.loads((P/'http.json').read_text());row={'name':'omega-final-delta','url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=18) as r:
  b=r.read(6*1024*1024);(P/'sources/omega-final-delta').write_bytes(b);j=json.loads(b);row.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),files=[x['filename'] for x in j.get('files',[])],commits=j.get('total_commits'))
except Exception as e:row['error']=str(e)
log.append(row);(P/'http.json').write_text(json.dumps(log,indent=2));print(row)
pat=re.compile(r'2410\.13920|Bernoulli structure|Fontana|Semeraro|2312\.01819|Tsallis.{0,70}heat|2111\.06997|varentropy',re.I)
rows=[]
for name in (P/'all-report-target-filenames.txt').read_text().splitlines():
 p=Path(name)
 if p.stat().st_size>8*1024*1024:rows.append({'path':name,'skipped':'over8MiB'});continue
 s=p.read_text(errors='replace');ms=list(pat.finditer(s));rows.append({'path':name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'sections':[s[max(0,m.start()-200):m.end()+500] for m in ms[:3]],'match_count':len(ms)})
(P/'all-report-bounded-sections.json').write_text(json.dumps(rows,indent=2))
print('bounded sections',len(rows))
