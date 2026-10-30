import sys,json,hashlib,datetime,urllib.request,re,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent
B=L.parents[1]
R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j): (L/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
if sys.argv[1]=='history':
 old=L.parent/'sol-fresh-source-discovery-r137/history-receipt.json'
 j=json.loads(old.read_bytes());paths=set(p for ps in j['aliases'].values() for p in ps)
 for lane in (B/'lanes').iterdir():
  if lane==L or not lane.is_dir():continue
  for f in lane.iterdir():
   if f.is_file() and f.name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str(f.relative_to(R)))
 pat=re.compile(sys.argv[2],re.I);hits=[];bodies={};missing=[];drift=[]
 known={p:h for h,ps in j['aliases'].items() for p in ps}
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();h=sha(b);bodies.setdefault(h,[]).append(p)
  if known.get(p)!=h:drift.append(p)
  s=b.decode(errors='replace')
  if pat.search(s):hits.append(dict(path=p,sha256=h,matches=[s[max(0,m.start()-130):m.end()+230] for m in pat.finditer(s)]))
 for n in ['ledger.json','prior-campaign-context.json']:
  s=(B/n).read_text()
  if pat.search(s):hits.append(dict(path=str(B/n),matches=[m.group() for m in pat.finditer(s)]))
 save('history-'+sys.argv[3]+'.json',dict(pattern=pat.pattern,retained=str(old),retained_sha256=sha(old.read_bytes()),complete_bodies=len(bodies),paths=len(paths),missing=missing,new_or_changed=drift,hits=hits,aliases=bodies,cutoff=None,limits='Retained original-role r137 coverage plus immediate batch lane original reports. No whole-r111-r113 exclusion. No nested newly created reports outside retained paths; no semantic absence claim.'))
 print('history',len(bodies),'bodies',len(hits),'hits');print(json.dumps(hits,ensure_ascii=False,indent=2))
elif sys.argv[1]=='fetch':
 for arg in sys.argv[2:]:
  name,url=arg.split('=',1);r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-research/1.0'}),timeout=35) as f:
    b=f.read(12000001)
    if len(b)>12000000:raise ValueError('12 MB response cap')
    (L/'sources'/name).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif sys.argv[1]=='text':
 for n in sys.argv[2:]:
  p=subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/n.replace('.pdf','.txt'))],capture_output=True)
  print(n,p.returncode,p.stderr.decode())
elif sys.argv[1]=='context':
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  print(n,len(b),sha(b))
  if n.endswith('.json'):
   j=json.loads(b);print(list(j));print(str(j)[:3500])
elif sys.argv[1]=='html':
 from html.parser import HTMLParser
 class P(HTMLParser):
  def handle_data(self,s):self.out.append(s)
 for n in sys.argv[2:]:
  p=P();p.out=[];p.feed((L/'sources'/n).read_text());(L/'sources'/n.replace('.html','.txt')).write_text('\n'.join(p.out))
elif sys.argv[1]=='delta':
 j=json.loads((L/'sources/omega-compare.json').read_bytes())
 r={k:j[k] for k in ['status','ahead_by','behind_by','total_commits']}
 r.update(base=j['base_commit']['sha'],merge_base=j['merge_base_commit']['sha'],commits=len(j['commits']),files=len(j['files']),paths=[f['filename'] for f in j['files']])
 r['caps_ok']=r['commits']==r['total_commits'] and r['files']<300 and r['commits']<250
 r['ancestry_ok']=r['merge_base']==r['base'] and r['status']=='ahead'
 save('registry-delta-receipt.json',r);print(json.dumps(r,indent=2))
elif sys.argv[1]=='treedelta':
 base='aa026efa802f4361758b827d6b68231ac353948f';head='a19a578cd06b57a4ea4d287cb0df92f9085117ae'
 calls=[];changed=[];pending=[]
 def get(ref):
  if len(calls)>=40:raise RuntimeError('40 tree request bound')
  url='https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+ref
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(2500000)
  n='tree-'+ref+'.json';(L/'sources'/n).write_bytes(b);j=json.loads(b)
  calls.append(dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),name=n,bytes=len(b),sha256=sha(b),truncated=j.get('truncated')))
  if j.get('truncated'):raise RuntimeError('truncated direct tree')
  return {x['path']:x for x in j['tree']}
 def walk(path,a,b):
  if a==b:return
  aa=get(a) if a else {};bb=get(b) if b else {}
  for n in sorted(aa.keys()|bb.keys()):
   x=aa.get(n,{});y=bb.get(n,{});p=(path+'/'+n).lstrip('/')
   if x.get('sha')==y.get('sha'):continue
   if not path and n not in {'Blueprint','Library','Problems','README.md'}:continue
   if (x.get('type') or y.get('type'))=='tree':walk(p,x.get('sha'),y.get('sha'))
   elif p.endswith('.md'):changed.append(dict(path=p,old=x.get('sha'),new=y.get('sha')))
 try:walk('',base,head)
 except Exception as e:pending.append(str(e))
 save('registry-relevant-tree-delta.json',dict(base=base,head=head,calls=calls,changed=changed,failures=pending,scope=['Blueprint/**/*.md','Library/**/*.md','Problems/**/*.md','README.md'],limits='Only source-facing Markdown scopes. Excludes metadata atoms, generated formal code, non-Markdown, other root directories; no full historic or repository semantic clearance.'))
 print('requests',len(calls),'changed',len(changed),'failures',pending);print(json.dumps(changed,indent=2))
