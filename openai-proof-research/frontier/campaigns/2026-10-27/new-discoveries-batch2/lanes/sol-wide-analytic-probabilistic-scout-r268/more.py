from work import *
import urllib.parse
for a in ['1808.05936v2','2608.17321v1']:
 p=fetch('https://arxiv.org/pdf/'+a,a+'.pdf');q=freeze(p);subprocess.run(['pdftotext','-layout',str(q),str(L/'science'/(a+'.txt'))],check=True)
for name,q in [('valent-correct','ti:Valent AND cat:math.CA'),('helly-specific','all:"centrally symmetric convex position"'),('j-specific','ti:"Santalo" AND au:Saroglou')]:
 p=fetch('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&max_results=20&sortBy=submittedDate&sortOrder=descending',name+'.xml');freeze(p)
