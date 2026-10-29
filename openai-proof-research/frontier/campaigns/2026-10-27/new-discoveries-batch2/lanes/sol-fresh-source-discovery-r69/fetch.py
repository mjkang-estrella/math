import urllib.request,json,hashlib,datetime,pathlib
base=pathlib.Path(__file__).parent
urls={
'palmer.html':'https://mathoverflow.net/questions/476529/distribution-class-closed-under-convolution-counterexample',
'palmer-profile.html':'https://mathoverflow.net/users/japalmer',
'distance.html':'https://mathoverflow.net/questions/509554/is-the-expected-distance-between-two-random-interior-points-of-a-convex-body-alw',
'shen-v3.html':'https://arxiv.org/html/2608.06470v3',
'brascamp-lieb.pdf':'https://fig.if.usp.br/~marchett/rg/some-inequalities-gaussian-measures_brascamp-lieb.pdf',
'registry-independent.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3/Problems/metya-mukherjee-independent-convolution-l1.md',
'registry-independent.lean':'https://raw.githubusercontent.com/the-omega-institute/trureturing/6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3/D5/S3/TotalVariation/IndependentConvolutionL1Minimum.lean'
}
with (base/'http.jsonl').open('a') as log:
 for name,url in urls.items():
  row={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':'sources/'+name}
  try:
   with urllib.request.urlopen(url,timeout=35) as r: data=r.read();row.update(status=r.status,headers=dict(r.headers))
   (base/'sources'/name).write_bytes(data);row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  except Exception as e:row['error']=str(e)
  log.write(json.dumps(row)+'\n');log.flush();print(name,row.get('status',row.get('error')))
