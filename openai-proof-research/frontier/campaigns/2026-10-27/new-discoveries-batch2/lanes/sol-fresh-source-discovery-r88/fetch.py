import pathlib,urllib.request,json,hashlib,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent
S=L/'sources';S.mkdir(exist_ok=True)
urls={'narayana':'https://cfc.nankai.edu.cn/_upload/article/files/ca/07/264e89bc4d9bb418a6d91d482b90/ef62459f-bec2-470d-8199-b57a790de20a.pdf','toeplitz':'https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/tem2.pdf','spread':'https://statics.scnu.edu.cn/pics/userfiles/2024/1211/20241211090841220.pdf'}
log=[]
for k,u in urls.items():
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=35) as f: b=f.read(8*1024*1024);r.update(status=f.status,final_url=f.url)
  (S/(k+'.pdf')).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());subprocess.run(['pdftotext','-layout',str(S/(k+'.pdf')),str(S/(k+'.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 log.append(r)
(L/'http.json').write_text(json.dumps(log,indent=2))
# Read complete administrative JSON; preserve compact substantive entries and hashes.
B=L.parent.parent;out={}
for p in [B/'ledger.json',B/'prior-campaign-context.json']:
 b=p.read_bytes();j=json.loads(b);out[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'accepted':j.get('accepted'),'excluded':j.get('excluded'),'held_candidates':j.get('held_candidates'),'candidates':j.get('candidates')}
(L/'context.json').write_text(json.dumps(out,indent=2))
print(json.dumps(log,indent=2))
