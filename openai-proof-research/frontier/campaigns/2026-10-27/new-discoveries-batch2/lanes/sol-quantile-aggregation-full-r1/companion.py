exec((__import__('pathlib').Path(__file__).parent/'retrieve.py').read_text().split('for name,url in queries:')[0])
queries=[('wang-papers','https://sas.uwaterloo.ca/~wang/papers.html'),('joint-query','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('ti:"Joint mixability"')+'&max_results=10'),('convolution','https://arxiv.org/pdf/2007.09320')]
exec((L/'retrieve.py').read_text().split('for name,url in queries:')[1].join(['for name,url in queries:','']))
