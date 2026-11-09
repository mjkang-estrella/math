from research import *
import xml.etree.ElementTree as E
ns={'a':'http://www.w3.org/2005/Atom'}
for key in ['bmv','qtspp','shapiro']:
 entries=E.parse(L/'primary'/(key+'.atom')).findall('a:entry',ns)
 for e in entries:print(key,e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
 if key=='shapiro':continue
 e=entries[0];id=e.findtext('a:id',namespaces=ns).split('/abs/')[1];pdf=id.replace('/','-')+'.pdf'
 files=[str(p) for p in L.parent.glob('*/*.md') if p.parent!=L and p.name in ['SUMMARY.md','SCOUTING.md','discovery.md']]
 pat='BMV|Bessis.Moussa.Villani|'+id.split('v')[0] if key=='bmv' else 'q.TSPP|totally symmetric plane partition|'+id.split('v')[0]
 r=subprocess.run(['rg','-il',pat,*files],capture_output=True,text=True);log('alias-checks.jsonl',dict(pattern=pat,paths=r.stdout.splitlines(),scope='direct lane reports'))
 fetch(pdf,'https://arxiv.org/pdf/'+id)
 if (L/'primary'/pdf).exists():extract(L/'primary'/pdf)
out=[]
for e in E.parse(L/'primary'/'breadth-current.atom').findall('a:entry',ns):out.append(dict(id=e.findtext('a:id',namespaces=ns),published=e.findtext('a:published',namespaces=ns),updated=e.findtext('a:updated',namespaces=ns),title=e.findtext('a:title',namespaces=ns)))
(L/'chronology.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
