import json,pathlib,subprocess,hashlib,datetime,re
L=pathlib.Path(__file__).resolve().parent;B=L.parent;S=L/'sources';rows=json.loads((L/'records.json').read_text());out=[];failure=[]
ids={x['record']['mathdb_id'] for x in rows}; excluded=set()
def walk(o):
 if isinstance(o,dict):
  for k,v in o.items():
   if k in ('mathdb_id','problem_id') and isinstance(v,int):excluded.add(v)
   elif k in ('mathdb_ids','problem_ids') and isinstance(v,list):excluded.update(x for x in v if isinstance(x,int))
   walk(v)
 elif isinstance(o,list):
  for v in o:walk(v)
for fn in ['accepted-exclusions.json','historical-dispositions.json']:walk(json.loads((B/'root-mathdb-accepted-exclusions-r304'/fn).read_text()))
assert not ids&excluded,ids&excluded
(L/'association-check.json').write_text(json.dumps({'status':'PASS','assigned':50,'excluded_association_ids':len(excluded),'intersection':sorted(ids&excluded)},indent=2)+'\n')
urls=sorted({x['record']['source_url'] for x in rows});park=False
for url in urls:
 key=url.rsplit('/',1)[-1];pdf=S/(key+'.pdf');h=S/(key+'.headers');u='https://arxiv.org/pdf/'+key
 if park:failure.append({'url':u,'status':'HOLD','reason':'domain parked after 403/429/challenge'});continue
 if not pdf.exists():
  p=subprocess.run(['curl','-sS','-L','--max-time','18','-D',str(h),'-o',str(pdf),'-w','%{http_code}',u],capture_output=True,text=True)
  code=p.stdout[-3:]
  if p.returncode or code!='200':
   failure.append({'url':u,'http':code,'exit':p.returncode,'stderr':p.stderr,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
   if code in ['403','429']:park=True
   continue
 b=pdf.read_bytes()
 if not b.startswith(b'%PDF'):
  failure.append({'url':u,'reason':'non-PDF; possible challenge; parked'});park=True;continue
 t=S/(key+'.txt');subprocess.run(['pdftotext','-layout',str(pdf),str(t)],check=True)
 out.append({'url':u,'version':'served PDF; version identifier must be read from cover; unpinned until then','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pdf':str(pdf),'pdf_sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'text':str(t),'text_sha256':hashlib.sha256(t.read_bytes()).hexdigest(),'read_level':'not yet read','proof_audit':False})
(L/'sources.json').write_text(json.dumps(out,indent=2)+'\n');(L/'failures.json').write_text(json.dumps(failure,indent=2)+'\n')
print('sources retained and hashed before content',len(out),'failures',len(failure))
