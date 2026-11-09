import pathlib,urllib.request,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1]
def get(name,url):
 r={'url':url,'utc':str(datetime.datetime.now(datetime.timezone.utc))}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research source verification'}),timeout=25) as f: b=f.read();r['status']=f.status
  (D/'sources'/name).write_bytes(b);r['sha256']=hashlib.sha256(b).hexdigest()
 except Exception as e:r['error']=str(e)
 (D/'sources'/(name+'.receipt.json')).write_text(json.dumps(r,indent=2));print(r,flush=True)
 return r

get('author.pdf','https://zhangbiaomath.github.io/papers/2024-dam-separable-perms.pdf')
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
get('omega-library.md',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/Library/PermutationPatterns/chenkitaevzhang2024separable.md')
