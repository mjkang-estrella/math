from work import *
from urllib.parse import quote
if sys.argv[1]=='current':
 urls=[('https://cs.uwaterloo.ca/journals/JIS/VOL21/Stipulanti/stip8.pdf','current-stip8.pdf'),('https://arxiv.org/pdf/1803.00292','merta-bs.pdf'),('https://arxiv.org/pdf/1810.03533','merta-general.pdf'),('https://www.m.stipulanti.uliege.be/publications.html','stipulanti-publications.html'),('https://export.arxiv.org/api/query?search_query='+quote('all:"period-doubling" AND (au:Stipulanti OR au:Merta OR au:Rampersad)')+'&max_results=25','author-search.xml')]
 for u,n in urls:fetch(u,n)
elif sys.argv[1]=='history':
 aliases=['period.doubling','A317544','Baum.Sweet','Merta','Stipulanti']
 import re
 hits=[];refs=[]
 for p in sorted((B/'lanes').glob('*/*')):
  if p.name not in ['SUMMARY.md','SCOUTING.md','discovery.md','FAILURES.md']:continue
  if p.parent==L:continue
  h=sha(p);s=p.read_text(errors='replace');assert sha(p)==h
  refs.append({'path':str(p),'sha256':h})
  found=[s[max(0,m.start()-120):m.end()+260] for a in aliases for m in list(re.finditer(a,s,re.I))[:5]]
  if found:hits.append({'path':str(p),'sha256':h,'passages':found})
 dump('history-screen.json',{'scope':'all immediate lane reports with four exact filenames; no recursive archives or bodies','aliases':aliases,'references':refs,'hits':hits})
 print(json.dumps(hits,indent=2)[:27000])
elif sys.argv[1]=='bodies':
 for n in ['merta-bs','merta-general']:
  p=next(L.glob('frozen/*/'+n+'.pdf'));h=sha(p);out=L/'texts'/(n+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(out)],check=True);assert sha(p)==h
  s=out.read_text(); print('\nBODY',n,'\n',s[:1800])
  import re
  for m in re.finditer(r'Theorem 2.6|zero|regular|question|problem|Conjecture',s,re.I):
   if 'regular' in m.group().lower() and n=='merta-general':continue
   print(s[max(0,m.start()-180):m.end()+700])
elif sys.argv[1]=='index':
 fetch('https://cs.uwaterloo.ca/journals/JIS/vol17.html','jis17.html')
elif sys.argv[1]=='indexread':
 import re
 p=next(L.glob('frozen/*/jis17.html'));print(p.read_text()[:110000])
elif sys.argv[1]=='breadth':
 import re
 s=next(L.glob('frozen/*/jis17.html')).read_text()
 links=list(dict.fromkeys(re.findall(r'href="([^"]+\.pdf)"',s,re.I)))
 selected=[x for x in links if any(a.lower() in x.lower() for a in ['Larsson','Hull','Allen','Subedi','Mezo','Hu/','Ballot','Kitaev','Barbero','Dresden','Carroll','Doslic','Martinjak','Alvarado','Lang/','Smith','Nyblom','Heyman','Melham','Tengely','Zheng'])]
 dump('breadth-selection.json',selected)
 for x in selected:
  if not x.startswith('http'):x='https://cs.uwaterloo.ca/journals/JIS/'+x
  fetch(x,'breadth-'+x.split('/')[-1])
elif sys.argv[1]=='breadthread':
 import re
 for p in L.glob('frozen/*/breadth-*.pdf'):
  h=sha(p);out=L/'texts'/(p.stem+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(out)],check=True);assert sha(p)==h
  s=out.read_text();passages=[]
  for m in re.finditer(r'Conjecture\s+\d|Question\s+\d|Problem\s+\d|open problem|open question',s,re.I):passages.append(s[max(0,m.start()-220):m.end()+1800])
  print('\nFILE',p.name,'\n',s[:320], '\nPASSAGES\n','\n'.join(passages)[:13000])
elif sys.argv[1]=='searchmore':
 for q,n in [('au:Merta','merta-current.xml'),('all:"A317544"','oeis-alias.xml'),('all:"inverse" AND all:"period-doubling"','inverse-current.xml')]:fetch('https://export.arxiv.org/api/query?search_query='+quote(q)+'&max_results=50',n)
elif sys.argv[1]=='breadth2':
 import re
 s=next(L.glob('frozen/*/jis17.html')).read_text()
 for x in dict.fromkeys(re.findall(r'href="([^"]+\.pdf)"',s,re.I)):
  if any('/'+a+'/' in x for a in ['Eroh','Ismailescu','Avila','Jubin','Lansing','Khovanova','Cloutier','Broughan','Currie']):fetch('https://cs.uwaterloo.ca/journals/JIS/'+x,'breadth-'+x.split('/')[-1])
elif sys.argv[1]=='breadthcurrent':
 for q,n in [('all:"Fubini" AND all:"period"','fubini'),('all:"Wythoff" AND all:"splitting"','wythoff'),('all:"kneading" AND all:"quadratic"','kneading'),('all:"largest" AND all:"Stern"','stern'),('all:"free Fibonacci"','freefib'),('all:"prisoners" AND all:"guards"','guards')]:fetch('https://export.arxiv.org/api/query?search_query='+quote(q)+'&max_results=15',n+'-current.xml')
elif sys.argv[1]=='breadthhistory':
 import re
 aliases=['Fubini','Mez[oőö]','kneading','Lansing','largest values.*Stern','Wythoff','Larsson','free Fibonacci','Avila','prisoners','guards','semiorder','Miura']
 refs=[];hits=[]
 # Freeze each immediate report individually before scientific reading; no historical subtrees.
 for p in sorted((B/'lanes').glob('*/*')):
  if p.name not in ['SUMMARY.md','SCOUTING.md','discovery.md']:continue
  if p.parent==L:continue
  # A compact local source snapshot is required here; hashes alone do not freeze bytes.
  q=freeze(p);s=q.read_text(errors='replace')
  found=[{'alias':a,'passage':s[max(0,m.start()-80):m.end()+150]} for a in aliases for m in list(re.finditer(a,s,re.I))[:2]]
  if found:hits.append({'original':str(p),'sha256':sha(q),'hits':found})
 dump('breadth-history.json',{'scope':'three immediate report names, all lanes; frozen individual files only, no recursive trees','aliases':aliases,'hits':hits})
 print(json.dumps(hits,indent=2)[-22000:])
