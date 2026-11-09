from research import *
import xml.etree.ElementTree as E
ns={'a':'http://www.w3.org/2005/Atom'}
for key in ['shuffle-spectrum','magnitude-successor','stanleydepth-successor','shannon-successor']:
 for e in E.parse(L/'primary'/(key+'.atom')).findall('a:entry',ns):print(key,e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
fetch('infinite-log.atom','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('ti:"log-concavity" AND au:McNamara')+'&max_results=5')
fetch('delta-proof.atom','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('ti:"Delta conjecture" AND (au:D%27Adderio OR au:Mellit)')+'&max_results=5')
for id in ['1507.02502v2','1504.04279v3','2410.02545v1']:
 fetch(id+'.pdf','https://arxiv.org/pdf/'+id)
 if (L/'primary'/(id+'.pdf')).exists():extract(L/'primary'/(id+'.pdf'))
patterns=['0908.1582','0811.0949','0712.2308','1509.07058','0408312','0608021','1008.4707','infinite log.concav']
records=[]
for pattern in patterns:
 files=[str(p) for p in L.parent.glob('*/*.md') if p.parent!=L and p.name in ['SUMMARY.md','SCOUTING.md','discovery.md']]
 r=subprocess.run(['rg','-il',pattern,*files],capture_output=True,text=True)
 hits=r.stdout.splitlines();records.append(dict(pattern=pattern,paths=hits))
 for path in hits:
  p=pathlib.Path(path);d=L/'dedup-frozen'/p.parent.name/p.name;d.parent.mkdir(parents=True,exist_ok=True);h=sha(p);d.write_bytes(p.read_bytes());assert sha(d)==h==sha(p)
  log('sourcebindings.jsonl',dict(source=str(p),copy=str(d),source_sha256=h,text_sha256=h))
(L/'early-targeted-dedup.json').write_text(json.dumps(records,indent=2));print('TARGETED DEDUP',json.dumps(records))
