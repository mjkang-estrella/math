from pathlib import Path
import hashlib,json,subprocess,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(row):
 assert sha(Path(row['original']))==row['sha256']==sha(Path(row['copy'])),row
m=json.loads((L/'finalmanifest.json').read_text())
for row in m['files']:
 p=L/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],row
b=json.loads((L/'bindings.json').read_text())
for row in b['scientific']:verify(row)
for row in json.loads((L/'access.json').read_text()):
 if 'sha256' in row:verify(row)
broader=json.loads((L/'broader-access.json').read_text());verify(broader);verify(broader['text'])
extract=[]
for ident in ['2304.01145v2','1202.3900v1','1003.4856v2']:
 pdf=L/'frozen'/'primary'/(ident+'.pdf');txt=L/'frozen'/'texts'/(ident+'.txt')
 data=subprocess.run(['pdftotext','-layout',str(pdf),'-'],check=True,stdout=subprocess.PIPE).stdout
 assert hashlib.sha256(data).hexdigest()==sha(txt),ident
 extract.append(ident)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':sha(L/'finalmanifest.json'),'manifest_files':len(m['files']),'original_copy_after_checks':len(b['scientific'])+4,'fresh_pdf_text_matches':extract,'administrative':'snapshot only','scope':'artifact verification, not a proof certificate; root alone accepts/counts'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
