from fetch import fetch
import urllib.parse,json
queries={'power-log':'log concavity partitions into kth powers Ulas','entropoid-break':'Entropoid Based Cryptography attack','hook-local':'Local Limit Theorems for Hook Lengths in Partitions','peak-hurwitz':'Hurwitz stable Stirling Tn r peak polynomials','snake':'Triangulations generalized snake posets turns dual graph','gapfree':'regularity powers gap free graphs conjecture symbolic ordinary Minh Vu'}
for k,q in queries.items():
 fetch('https://api.openalex.org/works?search='+urllib.parse.quote(q)+'&per-page=5',k+'-search.json')
 j=json.load(open('sources/'+k+'-search.json'));print(k,[(r['title'],r.get('doi'),[(x.get('landing_page_url'),x.get('pdf_url'))for x in r['locations']])for r in j['results']])
