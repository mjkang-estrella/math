import pathlib,json,urllib.request,hashlib,datetime,re
D=pathlib.Path(__file__).resolve().parents[1];out={}
def fetch(label,url):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest())
  (D/f'sources/{label}.json').write_bytes(b);o=json.loads(b)
 except Exception as e:r['error']=str(e);o={}
 (D/f'sources/{label}.receipt.json').write_text(json.dumps(r,indent=2))
 return o
head=json.loads((D/'sources/registry-trureturing.json').read_text())['sha']
root=fetch('omega-root','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+head)
for scope in ['D5','Problems']:
 entry=next((x for x in root.get('tree',[]) if x['path']==scope),None)
 if entry:
  o=fetch('omega-'+scope,'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+entry['sha']+'?recursive=1')
  paths=[x['path'] for x in o.get('tree',[])]
  out[scope]={'truncated':o.get('truncated'),'paths':len(paths),'hits':[p for p in paths if re.search('Nanostar|Totient|Ghanbari|Cordial|Mousley|Interweav|Mammoliti|Hamming|Ryser|347772|349177',p,re.I)]}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
