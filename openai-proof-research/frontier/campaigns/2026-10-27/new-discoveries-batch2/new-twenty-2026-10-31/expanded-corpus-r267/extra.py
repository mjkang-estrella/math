exec(open(__file__.replace('extra.py','fetch.py')).read().split('d=json.loads')[0])
d=json.loads((p/'literal-provenance.json').read_text());versions=json.loads((p/'version-inventory.json').read_text()); tasks=[]
for i,v in versions.items():
 a=d[i]['record']['source_url'].split('/abs/')[1]
 for n in v['versions'][:-1]:tasks.append((f'{i}-v{n}','https://arxiv.org/pdf/'+a+'v'+n))
for i,a in [('379909-Li','0805.0410'),('379212-later','0704.1914'),('319244-earlier','math/0509397'),('326327-earlier','math/0509470'),('324408-earlier','1002.1033'),('324408-old','math/0205047')]:tasks.append((i,'https://arxiv.org/pdf/'+a))
tasks += [('317269-journal','https://www.math.iitb.ac.in/~srg/preprints/Subclose-conm.pdf'),('378433-later','https://dmtcs.episciences.org/2382/pdf')]
# Registry URL reused from public receipt, no GitHub API.
r=json.loads((p.parent/'expanded-corpus-r266/sources/registry-projects.yml.receipt.json').read_text()) if (p.parent/'expanded-corpus-r266/sources/registry-projects.yml.receipt.json').exists() else {}
print('registry receipt',r,flush=True)
def get(t):
 name,url=t;r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  z=requests.get(url,timeout=7);r.update(status=z.status_code,bytes=len(z.content),sha256=hashlib.sha256(z.content).hexdigest());f=p/'sources'/f'{name}.pdf';f.write_bytes(z.content);r['file']=str(f)
  if z.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=12,check=True)
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,tasks):
  with (p/'receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r['name'],r.get('status'),r.get('error'),flush=True)
