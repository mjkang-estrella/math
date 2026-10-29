exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('urls=')[0])
log=json.loads((P/'http.json').read_text());head=json.loads((P/'heads.json').read_text())['omega']
jobs={'box-original.pdf':'https://arxiv.org/pdf/2304.08335v1','omega-from-full-baseline.json':f'https://api.github.com/repos/the-omega-institute/trureturing/compare/1b999d9fda71df7537b62327147496d64a6f66ef...{head}','omega-convexity.md':f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/Blueprint/D5/S3/Analytic/Convexity/StrongConcavityAttainment.md'}
for n,u in jobs.items():
 r={'name':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=30) as f:b=f.read(16000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(P/'sources'/n).write_bytes(b)
  if n.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(P/'sources'/n),str(P/'sources'/(n+'.txt'))],check=True)
  if n.endswith('.json'):
   d=json.loads(b);r.update(compare_status=d.get('status'),total_commits=d.get('total_commits'),commits_returned=len(d.get('commits',[])),files_returned=len(d.get('files',[])),file_list_cap=300)
 except Exception as e:r['error']=str(e)
 log.append(r);print(n,r.get('status',r.get('error')))
(P/'http.json').write_text(json.dumps(log,indent=2))
