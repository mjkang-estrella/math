import pathlib,json,urllib.request,hashlib,subprocess
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i106_positive_characteristic_imm';E=S/'external';E.mkdir(exist_ok=True)
urls={'forbes':'https://drops.dagstuhl.de/storage/00lipics/lipics-vol300-ccc2024/LIPIcs.CCC.2024.31/LIPIcs.CCC.2024.31.pdf','agkst':'https://arxiv.org/pdf/2211.07691v1','lst':'https://eccc.weizmann.ac.il/report/2021/081/revision/1/download/','abt':'https://eccc.weizmann.ac.il/report/2026/104/download/','bera':'https://drops.dagstuhl.de/storage/00lipics/lipics-vol033-ccc2015/LIPIcs.CCC.2015.183/LIPIcs.CCC.2015.183.pdf'}
records=[]
for key,url in urls.items():
 try:
  with urllib.request.urlopen(url,timeout=45) as r:data=r.read();final=r.url
  (E/(key+'.pdf')).write_bytes(data)
  proc=subprocess.run(['pdftotext','-layout',str(E/(key+'.pdf')),str(E/(key+'.txt'))],capture_output=True,text=True)
  records.append({'name':key,'url':url,'resolved_url':final,'sha256':hashlib.sha256(data).hexdigest(),'extraction_exit':proc.returncode,'stderr':proc.stderr,'text_sha256':hashlib.sha256((E/(key+'.txt')).read_bytes()).hexdigest() if proc.returncode==0 else None})
 except Exception as e:records.append({'name':key,'url':url,'error':repr(e)})
 (S/'external-requests.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2))
