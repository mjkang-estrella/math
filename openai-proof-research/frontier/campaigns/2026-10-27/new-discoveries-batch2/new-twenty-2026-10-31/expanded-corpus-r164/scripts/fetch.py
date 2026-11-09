import urllib.request,urllib.error,json,hashlib,datetime,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
def fetch(url,name):
 p=D/'sources'/name
 assert not p.exists(),p
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':str(p)}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematics-research/1.0'}),timeout=25) as r:
   b=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest());p.write_bytes(b)
 except Exception as e:rec['error']=str(e)
 with (D/'outputs/http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec),flush=True)
 return json.loads(b) if 'status' in rec and name.endswith('.json') else None
if __name__=='__main__':
 for repo in ['Vilin97/lean-pool','the-omega-institute/trureturing','openai/math']:
  tag=repo.replace('/','-');o=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',tag+'-head.json')
  if o:fetch('https://api.github.com/repos/'+repo+'/git/trees/'+o['sha']+'?recursive=1',tag+'-tree.json')
