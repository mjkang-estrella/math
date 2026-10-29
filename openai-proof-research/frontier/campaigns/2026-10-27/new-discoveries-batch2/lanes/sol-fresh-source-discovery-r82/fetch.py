import urllib.request,urllib.error,json,hashlib,datetime
from pathlib import Path
P=Path(__file__).resolve().parent
urls={
'dewitt.html':'https://arxiv.org/html/2507.13566v1',
'dewitt-abs.html':'https://arxiv.org/abs/2507.13566',
'followup.html':'https://arxiv.org/html/2604.25394v1',
'bias.html':'https://link.springer.com/article/10.1007/s40687-025-00502-0',
'fayers.html':'https://arxiv.org/html/2508.00074v1',
'journal.html':'https://www.worldscientific.com/doi/10.1142/S1793042126500569',
'omega-page.html':'https://github.com/the-omega-institute/trureturing',
'openai-page.html':'https://github.com/openai/math',
'omega-divisor.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/1b999d9fda71df7537b62327147496d64a6f66ef/Blueprint/D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound.md',
'omega-partition.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/1b999d9fda71df7537b62327147496d64a6f66ef/Blueprint/D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.md',
}
log=[]
for name,url in urls.items():
 row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:
   b=r.read(12000000);row.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(b).hexdigest());(P/'sources'/name).write_bytes(b)
 except Exception as e:row['error']=str(e)
 log.append(row)
(P/'http.json').write_text(json.dumps(log,indent=2))
print(json.dumps([{k:v for k,v in r.items() if k not in ['headers']} for r in log],indent=2))
