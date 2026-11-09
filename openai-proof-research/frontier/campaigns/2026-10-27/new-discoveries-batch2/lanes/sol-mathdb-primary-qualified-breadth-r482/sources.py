import pathlib,json,hashlib,urllib.request,urllib.error,datetime,subprocess
O=pathlib.Path(__file__).resolve().parent;L=O.parent
rows=json.loads((O/'assigned-records.json').read_text()); ids={r['record']['mathdb_id'] for r in rows}
# Frozen history is read only after freeze has completed.
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 obj=json.loads((O/'frozen/root-mathdb-accepted-exclusions-r304'/name).read_text());print(name,'top keys',list(obj)[:12]);
 (O/(name+'.assignment-scan.txt')).write_text('\n'.join(line for line in json.dumps(obj,ensure_ascii=False,indent=2).splitlines() if any(str(i) in line for i in ids)))
for name in ['ledger.json','prior-campaign-context.json']:
 obj=json.loads((L.parent/name).read_text());print(name,str(obj)[:1800])
urls=sorted({r['record']['source_url'].replace('/abs/','/pdf/') for r in rows}); provenance=[];blocked=False
(O/'sources').mkdir(exist_ok=True)
for u in urls:
 entry={'url':u,'retrieval_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if blocked:entry['status']='not_attempted_host_hold'
 else:
  try:
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Math research screening (no automated retries)'}),timeout=12) as response:data=response.read();entry['http_status']=response.status
   p=O/'sources'/(u.rsplit('/',1)[-1]+'.pdf');p.write_bytes(data);entry.update(path=str(p),size=len(data),sha256=hashlib.sha256(data).hexdigest(),status='bound_before_text_extraction')
   result=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True);entry['pdftotext_exit']=result.returncode
   if result.stderr:(O/'sources'/(p.stem+'.stderr')).write_text(result.stderr)
  except Exception as e:
   entry.update(status='failed',error=repr(e))
   if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):blocked=True
 provenance.append(entry)
 (O/'source-provenance.json').write_text(json.dumps(provenance,indent=2))
print('sources',len(urls),'received',sum('path' in p for p in provenance),'blocked',blocked)
