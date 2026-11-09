import pathlib,urllib.request,json,hashlib,datetime,subprocess
D=pathlib.Path(__file__).resolve().parent
urls={'registry':'https://api.github.com/repos/openai/math/commits/HEAD','delone':'https://d-nb.info/1342131894/34','quantum':'https://arxiv.org/pdf/2302.10244','two-generator':'https://ora.ox.ac.uk/objects/uuid%3A2b046c1c-0c5a-407f-b825-c731ca9e0fec/files/s9s161850g','unipotent':'https://arxiv.org/pdf/2305.11274'}
for name,url in urls.items():
 receipt=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=25) as r:
   raw=r.read(18000000);receipt.update(status=r.status,final_url=r.url,headers=dict(r.headers),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest());p=D/'sources'/(name+('.pdf' if raw.startswith(b'%PDF') else '.json'));p.write_bytes(raw)
   if raw.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=20)
 except Exception as e:receipt.update(error=str(e))
 (D/'sources'/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(name,receipt.get('status'),receipt.get('sha256'),receipt.get('error',''),flush=True)
