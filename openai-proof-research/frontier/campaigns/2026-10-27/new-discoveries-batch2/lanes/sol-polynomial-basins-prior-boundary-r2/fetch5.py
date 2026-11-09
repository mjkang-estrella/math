from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,subprocess
L=Path(__file__).resolve().parent
queries=[('locally-nilpotent','https://arxiv.org/pdf/2309.10303v1')]
exec(('receipts=[]'+(L/'fetch2.py').read_text().split('receipts=[]')[1]).replace('retrieval2.json','retrieval5.json'))
