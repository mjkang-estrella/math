import urllib.request,hashlib,json,datetime,pathlib
root=pathlib.Path(__file__).parent
urls={'murai.html':'https://arxiv.org/html/2609.18136v1','kien.html':'https://arxiv.org/html/2609.39218v1','chomicz.html':'https://arxiv.org/html/2609.04000v1','murai-abs.html':'https://arxiv.org/abs/2609.18136','kien-abs.html':'https://arxiv.org/abs/2609.39218','chomicz-abs.html':'https://arxiv.org/abs/2609.04000'}
rows=[]
for name,url in urls.items():
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=35) as r: b=r.read();row.update(status=r.status,final_url=r.url)
  (root/row['file']).write_bytes(b);row['sha256']=hashlib.sha256(b).hexdigest()
 except Exception as e:row['error']=repr(e)
 rows.append(row)
(root/'sources/fetch.json').write_text(json.dumps(rows,indent=2))
