import pathlib,json,urllib.request,hashlib,datetime,sys,subprocess,time
D=pathlib.Path(__file__).resolve().parents[1]
receipts=[]
def fetch(url,path):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematics-research-screen'}),timeout=18) as f:
   b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));path.write_bytes(b)
 except Exception as e:r['error']=str(e)
 receipts.append(r);(D/'outputs/fetch-receipts.json').write_text(json.dumps(receipts,indent=2));return r
if sys.argv[1]=='sources':
 for i,o in json.loads((D/'extracted.json').read_text()).items():
  p=D/'sources'/i;p.mkdir(exist_ok=True)
  r=fetch(o['source_url'].replace('/abs/','/pdf/'),p/'source.pdf')
  if r.get('status')==200:subprocess.run(['pdftotext','-layout',str(p/'source.pdf'),str(p/'source.txt')],check=False)
  print(i,r,flush=True)
elif sys.argv[1]=='pool':
 p=D/'sources/lean-pool';p.mkdir(exist_ok=True)
 r=fetch('https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD',p/'head.json')
 if r.get('status')==200:
  sha=json.loads((p/'head.json').read_text())['sha'];fetch(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/projects.yml',p/'projects.yml');fetch(f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{sha}?recursive=1',p/'tree.json')
  if (p/'tree.json').exists():
   for x in json.loads((p/'tree.json').read_text()).get('tree',[]):
    if x['path'].startswith('candidates/') and x['type']=='blob':
     q=p/x['path'];q.parent.mkdir(parents=True,exist_ok=True);fetch(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/'+x['path'],q)
 print(receipts,flush=True)
