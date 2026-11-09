from pathlib import Path
import json,hashlib,urllib.request,urllib.error,subprocess,datetime
L=Path(__file__).resolve().parent
def h(b):return hashlib.sha256(b).hexdigest()
bindings=[];hits={};failures=[]
terms=['sensitivity','Kadison','Erdős discrepancy','Erdos discrepancy','cap set','cap-set']
(L/'dedup-flat').mkdir(exist_ok=True)
for p in sorted(L.parent.glob('*/SCOUTING.md')):
 if p.parent==L:continue
 data=p.read_bytes();q=L/'dedup-flat'/f'{len(bindings):04d}.md';q.write_bytes(data)
 assert h(p.read_bytes())==h(q.read_bytes())==h(data)
 bindings.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h(data)))
 text=data.decode(errors='replace')
 found=[t for t in terms if t.lower() in text.lower()]
 if found:hits[str(p)]=found
(L/'dedup-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
(L/'dedup.json').write_text(json.dumps(dict(terms=terms,coverage='Top-level SCOUTING.md only; no recursive histories, no global completeness claim',hits=hits),indent=2)+'\n')
print('DEDUP',json.dumps(hits),flush=True)
# These are separate original question families with actual later solution bodies.
# Retire immediately on a semantic historical match rather than analysing again.
candidates=[('sensitivity','1907.00847v1'),('Kadison','1306.3969v1'),('discrepancy','1509.05363v1'),('cap','1605.09223v1')]
access=[];(L/'sources').mkdir(exist_ok=True)
for name,ident in candidates:
 if any(name.lower() in t.lower() for ts in hits.values() for t in ts):
  failures.append(dict(family=name,reason='early alias hit: historical duplicate; skipped'))
  continue
 url='https://arxiv.org/pdf/'+ident
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'research-review/1.0'})
  with urllib.request.urlopen(req,timeout=25) as r:
   data=r.read(12*1024*1024);status=r.status
  if not data.startswith(b'%PDF'):raise ValueError('non-PDF response; stop this endpoint')
  p=L/'sources'/(ident+'.pdf');p.write_bytes(data)
  access.append(dict(url=url,status=status,time=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=str(p.relative_to(L)),sha256=h(data)))
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=20)
  txt=p.with_suffix('.txt');access.append(dict(derived_from=str(p.relative_to(L)),path=str(txt.relative_to(L)),sha256=h(txt.read_bytes())))
 except Exception as e:
  failures.append(dict(url=url,error=str(e),retry=False))
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):break
(L/'access.json').write_text(json.dumps(access,indent=2)+'\n')
(L/'failures.json').write_text(json.dumps(failures,indent=2)+'\n')
print('retrieved',len(access)//2,'failures',failures)
