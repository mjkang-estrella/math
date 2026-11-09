from fetch import get
from urllib.parse import quote
for key,url in [('2511.09718v1.html','https://arxiv.org/html/2511.09718v1'),('search-tree-title.xml','https://export.arxiv.org/api/query?search_query='+quote('ti:nearly AND ti:independent')+'&sortBy=lastUpdatedDate&sortOrder=descending&max_results=15'),('search-lamzouri.xml','https://export.arxiv.org/api/query?search_query='+quote('au:Lamzouri AND all:maximum')+'&sortBy=lastUpdatedDate&sortOrder=descending&max_results=5')]:print(get((key,url)),flush=True)
