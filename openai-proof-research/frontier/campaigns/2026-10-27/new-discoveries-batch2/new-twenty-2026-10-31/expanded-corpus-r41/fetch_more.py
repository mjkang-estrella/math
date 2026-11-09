exec(open(__file__.replace('fetch_more.py','fetch.py')).read().split('urls=')[0])
urls={'omega-correct-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',**{a:'https://arxiv.org/pdf/'+a for a in ['2011.11187v1','2012.11177v1','2012.09901v1','2011.03929','2012.02882','2012.01378']}}
for name,url in urls.items():
 receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  r=requests.get(url,timeout=25);b=r.content;receipt.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(p/'sources'/f'{name}.response').write_bytes(b)
  if b.startswith(b'%PDF'):
   (p/'sources'/f'{name}.pdf').write_bytes(b);subprocess.run(['pdftotext','-layout',str(p/'sources'/f'{name}.pdf'),str(p/'sources'/f'{name}.txt')],timeout=20,check=True)
 except Exception as e: receipt['error']=str(e)
 (p/'sources'/f'{name}.receipt.json').write_text(json.dumps(receipt,indent=2));print(name,receipt,flush=True)
