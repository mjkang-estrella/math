import urllib.request,datetime,pathlib,json,hashlib,sys
R=pathlib.Path(__file__).resolve().parents[1]
urls={
'journal.pdf':'https://arinaldo.github.io/papers/Eriksson_Fienberg_Rinaldo_Sullivant_2006.pdf',
'hjs.pdf':'https://arxiv.org/pdf/1112.1278',
'hjjs.pdf':'https://emis.muni.cz/journals/EJC/Volume_16/PDF/v16i2r6.pdf',
'splits.pdf':'https://arxiv.org/pdf/0805.0774',
'convex.pdf':'https://arxiv.org/pdf/math/0308254',
'extended.pdf':'https://www.stat.cmu.edu/~arinaldo/papers/Computing_Extended_MLE.pdf',
'openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD',
}
if len(sys.argv)>1: urls={sys.argv[1]:sys.argv[2]}
for name,url in urls.items():
 receipt={'utc':str(datetime.datetime.now(datetime.timezone.utc)),'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent-mathematics-review/1.0'}),timeout=30) as q:
   data=q.read(20000000);receipt.update(status=q.status,final_url=q.url,headers=dict(q.headers),sha256=hashlib.sha256(data).hexdigest());(R/'sources'/name).write_bytes(data)
 except Exception as e:receipt['error']=str(e)
 (R/'receipts'/('http-'+name+'.json')).write_text(json.dumps(receipt,indent=2));print(name,receipt.get('status',receipt.get('error')),flush=True)
