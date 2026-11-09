import pathlib,json,urllib.request,urllib.error,hashlib,datetime,subprocess,time
L=pathlib.Path(__file__).resolve().parent; (L/'sources').mkdir(exist_ok=True)
rs=json.loads((L/'assigned-records.json').read_text()); out=[]
# Source only, no MathDB access; stop entire host after access denial.
for ident in dict.fromkeys(x['record']['source_url'].rsplit('/',1)[-1] for x in rs):
 u='https://arxiv.org/pdf/'+ident; row={'url':u,'requested_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'served PDF; version to be read from body'}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research source inspection'}),timeout=12) as f:b=f.read(12000000); row['final_url']=f.url
  assert b.startswith(b'%PDF'), 'non-PDF body'
  p=L/'sources'/ (ident+'.pdf'); p.write_bytes(b); row.update({'file':str(p.relative_to(L)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
  q=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True,timeout=10); row['pdftotext_exit']=q.returncode
 except Exception as e:
  row['failure']=str(e)
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):
   out.append(row); print(row,flush=True); break
 out.append(row); print(row,flush=True)
(L/'source-receipts.json').write_text(json.dumps(out,indent=2)+'\n')
