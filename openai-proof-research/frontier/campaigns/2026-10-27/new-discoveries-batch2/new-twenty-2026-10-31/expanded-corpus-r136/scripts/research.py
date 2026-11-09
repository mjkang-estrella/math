import pathlib,json,hashlib,urllib.request,urllib.error,datetime,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1]; P=json.loads((D/'outputs/provenance.json').read_text())
def fetch(url,name):
 now=datetime.datetime.now(datetime.timezone.utc).isoformat(); receipt={'url':url,'utc':now}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=12) as r:
   b=r.read();receipt.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/f'sources/{name}').write_bytes(b)
 except Exception as e: receipt.update(error=str(e),status=getattr(e,'code',None))
 (D/f'sources/{name}.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n'); print(name,receipt)
mode=sys.argv[1]
if mode=='fetch':
 for i in sys.argv[2:]:
  a=P[i]['row']['source_url'].split('/')[-1];fetch('https://arxiv.org/abs/'+a,i+'.abs.html');fetch('https://arxiv.org/pdf/'+a,i+'.pdf')
  if (D/f'sources/{i}.pdf').exists(): subprocess.run(['pdftotext','-layout',str(D/f'sources/{i}.pdf'),str(D/f'sources/{i}.txt')],check=False)
elif mode=='history':
 ids=list(P); pat='|'.join(ids+['uniquely cycle-saturated','near-Eulerian','Matching-Jack','Dyck partitions','super-long-snake','safe.colouring','Heffter'])
 r=subprocess.run(['rg','-n','-i','--glob','*.md','--glob','*.json','--glob','*.txt','--glob','!mathdb*','--glob','!reservation.json','--glob','!TASK.txt',pat,str(D.parent.parent)],capture_output=True,text=True)
 lines=[l for l in r.stdout.splitlines() if '/expanded-corpus-r136/' not in l and '/routing-' not in l and '/corpus/' not in l and '/tags/' not in l]
 (D/'outputs/history.txt').write_text('\n'.join(lines)+'\n');print(len(lines),'history lines')
 for path in [D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
  obj=json.loads(path.read_text());(D/'outputs'/('read-'+path.parent.name+'-'+path.name)).write_text(json.dumps(obj,indent=2)+'\n')
  print(path,len(path.read_bytes()),hashlib.sha256(path.read_bytes()).hexdigest())
 for i in ids:
  print(i, '\n'.join(l[:700] for l in lines if i in l)[:3000])
elif mode=='registries':
 for repo in ['openai/math','the-omega-institute/trureturing']: fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',repo.replace('/','-')+'-HEAD.json')
elif mode=='url':
 for pair in sys.argv[2:]:
  name,url=pair.split('=',1);fetch(url,name)
elif mode=='trees':
 repo='the-omega-institute/trureturing';o=json.loads((D/'sources/the-omega-institute-trureturing-HEAD.json').read_text());head=o['sha'];fetch(f'https://api.github.com/repos/{repo}/git/trees/{head}','omega-root.json')
 root=json.loads((D/'sources/omega-root.json').read_text())
 for t in root['tree']:
  if t['path'] in ['D5','Problems']:fetch(f'https://api.github.com/repos/{repo}/git/trees/{t["sha"]}?recursive=1','omega-'+t['path']+'.json')
