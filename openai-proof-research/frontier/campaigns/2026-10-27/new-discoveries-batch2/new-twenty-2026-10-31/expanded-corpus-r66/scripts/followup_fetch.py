from fetch import get
from urllib.parse import quote
items=[('2510.00291.pdf','https://arxiv.org/pdf/2510.00291'),('2507.14568v1.html','https://arxiv.org/html/2507.14568v1')]
for key,q in [('tree','all:"nearly independent"'),('matching','all:"perfect matching association"'),('rigidity','all:"degree sum" AND all:rigidity')]:items.append((f'search-{key}.xml','https://export.arxiv.org/api/query?search_query='+quote(q)+'&sortBy=lastUpdatedDate&sortOrder=descending&max_results=10'))
for x in items:print(get(x),flush=True)
