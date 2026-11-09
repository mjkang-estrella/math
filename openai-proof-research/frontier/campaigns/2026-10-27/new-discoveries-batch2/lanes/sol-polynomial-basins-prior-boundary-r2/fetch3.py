from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
L=Path(__file__).resolve().parent
queries=[('nilpotent-polynomials','https://arxiv.org/pdf/2401.01435v3')]
exec(('receipts=[]'+(L/'fetch2.py').read_text().split('receipts=[]')[1]).replace("retrieval2.json","retrieval3.json"))
