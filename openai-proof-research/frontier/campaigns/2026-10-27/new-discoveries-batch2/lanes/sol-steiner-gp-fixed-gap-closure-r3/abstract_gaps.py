from work import *
for i in [10,19]:
 x=json.loads((L/'citation-abstracts.json').read_text())[i-1]
 b=fetch('https://api.semanticscholar.org/graph/v1/paper/DOI:'+x['doi'].split('doi.org/')[1]+'?fields=title,abstract,openAccessPdf',f'citations/{i}-s2.json')
 if b:print(i,b.decode())
 else:break
print('mathdb',[(x['number'],x['title']) for x in json.loads((R/'mathdb-search.json').read_text())['items'] if 'Steiner' in x['title']])
