from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,subprocess
L=Path(__file__).resolve().parent
queries=[('local-title','https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':'ti:"Locally nilpotent polynomials"','max_results':4}))]
exec(('receipts=[]'+(L/'fetch2.py').read_text().split('receipts=[]')[1]).replace('retrieval2.json','retrieval4.json'))
