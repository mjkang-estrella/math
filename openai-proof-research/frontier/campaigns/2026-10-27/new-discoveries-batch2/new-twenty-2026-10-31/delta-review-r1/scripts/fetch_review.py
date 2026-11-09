import urllib.request,urllib.error,pathlib,hashlib,json,datetime,sys
P=pathlib.Path(__file__).resolve().parents[1]
urls=sys.argv[1:]
for url in urls:
 out=P/'downloads'/('request-'+str(len(list((P/'downloads').iterdir()))).zfill(3));out.mkdir()
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'directory':str(out.relative_to(P))}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'IndependentMathematicsReview/1.0'}),timeout=12) as h:
   b=h.read(12000000);r.update(status=h.status,final_url=h.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(out/'body').write_bytes(b)
 except Exception as e:r['error']=str(e)
 (out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
