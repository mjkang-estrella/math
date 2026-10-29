import json, pathlib, hashlib, urllib.request, urllib.error, datetime, sys, time, re
O=pathlib.Path(__file__).resolve().parent
B=O.parent.parent
G=O.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
BASE='0d4df45e499f5e2d97471c506c555c18fd44920c'; HEAD='d254db264d94f6837888d045d5c12126faa84a5c'
API='https://api.github.com/repos/the-omega-institute/trureturing/'
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for chunk in iter(lambda:f.read(65536),b''):h.update(chunk)
 return h.hexdigest()
def save(n,j): (O/n).write_text(json.dumps(j,indent=2)+'\n')
def freeze(n):
 out={}
 for label,rel in [('candidate','root-renyi-final-review-freeze-r1/freeze.json'),('review','root-renyi-final-review-adoption-r1/review-freeze.json')]:
  p=O.parent/rel;j=json.loads(p.read_text()); actual={k:sha(pathlib.Path(j['root'])/k) for k in j['files']}
  out[label]={'descriptor':str(p),'descriptor_sha256':sha(p),'root':j['root'],'files':actual,'expected_count':len(j['files']),'mismatches':[k for k in actual if actual[k]!=j['files'][k]]}
 out['helper_guard_sha256']=sha(G)
 for p in [B/'NEXT.md',B/'lanes/root-renyi-final-review-adoption-r1/DECISION.md',B/'lanes/root-renyi-final-review-adoption-r1/ADOPTION.json']:
  if p.exists():out[str(p)]={'sha256':sha(p),'scope':'read-only context, not mathematical freeze'}
 save(n,out)
 assert all(not out[k]['mismatches'] for k in ['candidate','review'])
def fetch(url,name):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat(); start=time.monotonic(); dest=O/name;dest.parent.mkdir(exist_ok=True)
 req=urllib.request.Request(url,headers={'User-Agent':'bounded-targeted-research-review','Accept':'application/vnd.github+json'})
 try:r=urllib.request.urlopen(req,timeout=45)
 except urllib.error.HTTPError as e:r=e
 with r:
  h=hashlib.sha256();size=0
  with open(dest,'wb') as f:
   while True:
    c=r.read(65536)
    if not c:break
    size+=len(c)
    if size>24*1024*1024:raise RuntimeError('bounded response exceeds 24MiB')
    f.write(c);h.update(c)
  row={'url':url,'started_utc':t,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_s':time.monotonic()-start,'status':r.status,'headers':dict(r.headers),'file':name,'bytes':size,'sha256':h.hexdigest()}
 with open(O/'http.jsonl','a') as f:f.write(json.dumps(row)+'\n')
 print(r.status,name,size,r.headers.get('X-RateLimit-Remaining'),flush=True)
 if r.status!=200:raise RuntimeError('HTTP stop '+str(r.status))
 return dest
if __name__=='__main__':
 freeze('freeze-before.json')
 src=O.parent/'sol-renyi-threshold-full-final-review-r1/omega-fresh-delta.json';j=json.loads(src.read_text());cs={c['sha']:c for c in j['commits']};chain=[HEAD]
 while chain[-1]!=BASE:chain.append(cs[chain[-1]]['parents'][0]['sha'])
 chain.reverse();save('dag.json',{'source':str(src),'sha256':sha(src),'base':BASE,'head':HEAD,'first_parent_chain':chain,'listed_commits':[{'sha':c['sha'],'parents':[p['sha'] for p in c['parents']]} for c in j['commits']]})
 rows=[]
 for i,(a,b) in enumerate(zip(chain,chain[1:])):
  p=fetch(API+'compare/'+a+'...'+b,'responses/step-%02d.json'%i);d=json.loads(p.read_text())
  row={'base':a,'head':b,'response':str(p.relative_to(O)),'sha256':sha(p),'status':d['status'],'behind':d['behind_by'],'ahead':d['ahead_by'],'listed_commits':len(d['commits']),'total_commits':d['total_commits'],'listed_paths':len(d['files']),'merge_base':d['merge_base_commit']['sha']}
  rows.append(row);save('steps.json',rows)
  assert d['behind_by']==0 and d['merge_base_commit']['sha']==a and len(d['commits'])==d['ahead_by'] and d['ahead_by']<250
 print(json.dumps(rows,indent=2))
