import pathlib,json,hashlib,urllib.request,urllib.error,concurrent.futures,subprocess,datetime
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def fetch(x):
 p=x['path']; dest=S/'outside'/p;dest.parent.mkdir(parents=True,exist_ok=True)
 url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+urllib.parse.quote(p)
 row=dict(x,url=url,captured=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I79-research-source-audit/1.0'}),timeout=50) as r:
   b=r.read();row.update(status=r.status,headers=dict(r.headers),final_url=r.url)
  dest.write_bytes(b);row.update(local=str(dest.relative_to(R)),bytes=len(b),sha256=sha(b))
  row['git_match']=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['sha']
  if dest.suffix=='.pdf':
   out=subprocess.run(['pdftotext','-layout',str(dest),'-'],capture_output=True)
   text=dest.with_suffix('.pdf.txt');text.write_bytes(out.stdout)
   row['extraction']={'code':out.returncode,'stderr':out.stderr.decode(errors='replace'),'path':str(text.relative_to(R)),'sha256':sha(out.stdout)}
 except Exception as e:row['error']=repr(e)
 return row
if __name__=='__main__':
 inv=json.loads((R/'frontier/sources/i72_graph_probability_discovery/inventory.json').read_text())['other_blobs']
 with concurrent.futures.ThreadPoolExecutor(max_workers=16) as ex:
  with (S/'outside-requests.jsonl').open('w') as f:
   for k,row in enumerate(ex.map(fetch,inv),1):
    f.write(json.dumps(row,sort_keys=True)+'\n');f.flush()
    if k%100==0:print(k,flush=True)
 print('complete',len(inv),flush=True)
