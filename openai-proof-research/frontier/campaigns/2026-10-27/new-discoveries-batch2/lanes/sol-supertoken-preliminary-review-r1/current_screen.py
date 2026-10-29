from review_tools import *
import urllib.request,urllib.error,re
def get(url,name):
 stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent mathematical review'}),timeout=35) as f:
   raw=f.read(8*1024*1024+1);status=f.status;headers=dict(f.headers)
  assert len(raw)<=8*1024*1024
  (R/name).write_bytes(raw)
  rec={'url':url,'utc':stamp,'status':status,'path':name,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'remaining':headers.get('X-RateLimit-Remaining')}
 except urllib.error.HTTPError as e:
  rec={'url':url,'utc':stamp,'status':e.code,'error':str(e)};raw=None
 with (R/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 if rec['status'] in [403,429]:print(json.dumps(rec));sys.exit(0)
 print(json.dumps(rec));return raw
for repo,name in [('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
 raw=get('https://api.github.com/repos/'+repo+'/commits?per_page=1',name+'-head.json')
 if raw:
  d=json.loads(raw);print(name,'head',d[0]['sha'],d[0]['commit']['committer']['date'])
# Saved delta is original API response, not generated proof echo. Target-path screen only.
p=B/'lanes/sol-renyi-threshold-current-prior-review-r2/omega-delta.json'
d=json.loads(p.read_text());hits=[]
for f in d.get('files',[]):
 if re.search(r'supertoken|366438|2412.?20558|metric.?dimension|johnson|separating|multiset.?resolv',f['filename'],re.I):
  hits.append({'path':f['filename'],'status':f['status'],'patch_excerpt':f.get('patch','')[:5000]})
summary={'saved_delta_sha256':digest(p),'total_commits':d.get('total_commits'),'files_returned':len(d.get('files',[])),'missing_patches':sum('patch' not in f for f in d.get('files',[])),'target_matches':hits,'limitation':'Target filename screen; not semantic global clearance; older capped delta remains a gap.'}
(R/'registry-screen.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
