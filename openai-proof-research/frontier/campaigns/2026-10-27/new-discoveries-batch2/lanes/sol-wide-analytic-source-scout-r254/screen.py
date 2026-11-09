from pathlib import Path
import re,json,hashlib,urllib.request,urllib.parse,xml.etree.ElementTree as E
l=Path(__file__).resolve().parent;b=l.parent.parent
keys=['2304.01145','athreya','super-coupon','2305.02372','gomez','2304.02345','2304.10017','melzak','2304.10531','2305.00569','2305.03549','2203.14815','2103.11433','2101.10023','bahri','2010.14809','lieb-solovej','2211.14630','2012.15502','2004.05995','2104.08740']
rows=[];hits={k:[] for k in keys}
for lane in (b/'lanes').iterdir():
 if lane==l or not lane.is_dir():continue
 for p in lane.iterdir():
  if not p.is_file() or p.stat().st_size>170000 or p.suffix.lower() not in ['.md','.txt']:continue
  if not any(k in p.name.lower() for k in ['summary','scout','discovery','proof','review','decision','original']):continue
  d=p.read_bytes();h=hashlib.sha256(d).hexdigest();rows.append({'path':str(p),'sha256':h});t=d.decode(errors='replace').lower()
  for k in keys:
   if k in t:hits[k].append({'path':str(p.relative_to(b)),'snippet':t[max(0,t.index(k)-90):t.index(k)+180]})
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h
(l/'expanded-history-bindings.json').write_text(json.dumps(rows,indent=2));(l/'expanded-history-hits.json').write_text(json.dumps(hits,indent=2));print('EXPANDED',len(rows));print({k:v[:3] for k,v in hits.items() if v})
excerpts={}
for p in (l/'texts').iterdir():
 t=p.read_text();ms=list(re.finditer(r'(?im)^\s*Proof[. :]|Proof of Theorem|Proof of Proposition',t));excerpt='\n'.join(t[m.start():m.start()+1700] for m in ms[:2]);excerpts[p.stem]=excerpt;print('METHOD',p.stem,excerpt[:700].replace('\n',' '))
(l/'method-excerpts.json').write_text(json.dumps(excerpts,indent=2))
q='ti:"hitting" AND (ti:"rare" OR ti:"exponential")';u='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':10})
try:
 d=urllib.request.urlopen(u,timeout=25).read(2000000);h=hashlib.sha256(d).hexdigest();(l/'retrieved/rare.xml').write_bytes(d);(l/'frozen'/(h+'.xml')).write_bytes(d);(l/'rare-binding.json').write_text(json.dumps({'url':u,'sha256':h}));assert hashlib.sha256((l/'retrieved/rare.xml').read_bytes()).hexdigest()==h;ns={'a':'http://www.w3.org/2005/Atom'}
 for e in E.fromstring(d).findall('a:entry',ns):print('RARE',e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
except Exception as e:
 (l/'failures.jsonl').open('a').write(json.dumps({'url':u,'error':str(e)})+'\n');print(e)
