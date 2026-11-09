from retrieve import *
import re,html,urllib.parse
for cat,date in [('math.NT','202102'),('math.RA','202202')]:
 q=f'cat:{cat} AND submittedDate:[{date}010000 TO {date}282359]'
 p=fetch('https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'start':0,'max_results':65,'sortBy':'submittedDate','sortOrder':'ascending'}),cat+'.xml')
 if p:
  import xml.etree.ElementTree as E
  root=E.fromstring(p.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
  entries=[]
  for e in root.findall('a:entry',ns):
   j={k:' '.join(e.findtext('a:'+k,default='',namespaces=ns).split()) for k in ['id','title','summary','published','updated']};j['authors']=[x.findtext('a:name',namespaces=ns) for x in e.findall('a:author',ns)];entries.append(j)
  (L/(cat+'-entries.json')).write_text(json.dumps(entries,indent=2))
  for j in entries:print(j['id'],j['title'],j['summary'][:1000])
print((L/'retrieval.jsonl').read_text()[-4000:])
