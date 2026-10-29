import urllib.request,pathlib,datetime,json,hashlib
urls=[('pinelis-preprint.pdf','https://arxiv.org/pdf/math/0701806v1'),('figiel.pdf','https://www.ams.org/journals/tran/1997-349-03/S0002-9947-97-01789-3/S0002-9947-97-01789-3.pdf'),('pinelis1994.pdf','https://projecteuclid.org/journals/annals-of-statistics/volume-22/issue-1/Extremal-Probabilistic-Problems-and-Hotellings-T2-Test-Under-a/10.1214/aos/1176325373.pdf'),('registry-independent.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3/Problems/metya-mukherjee-independent-convolution-l1.md'),('registry-independent.lean','https://raw.githubusercontent.com/the-omega-institute/trureturing/6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3/D5/S3/TotalVariation/IndependentConvolutionL1Minimum.lean')]
for name,url in urls:
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=20) as f:b=f.read();r.update(status=f.status,headers=dict(f.headers))
  pathlib.Path(r['file']).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r['error']=str(e)
 with open('http.jsonl','a') as f:f.write(json.dumps(r)+'\n')
