import pathlib,json,re,hashlib,datetime,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent;C=L.parent;D=json.loads((L/'literal-records.json').read_text());pat=re.compile('|'.join(D)+r'|fair.?set|block.graph|partiality|Narkiewicz|zero.sum.free|cross.number|formation.width|unistructur|electrical.poset|internal.partition|Nielsen|Cookie.Monster|multiplicity.bounded|van.der.Waerden|Ryser|Brualdi|Ohba|synchroniz|stress.free',re.I)
out={}
for p in (C/'expanded-corpus-r253/http').iterdir():
 if p.name.endswith('.receipt.json') or not re.search('openai|omega|pool|projects',p.name):continue
 b=p.read_bytes();s=b.decode(errors='replace');tr=None
 try:
  d=json.loads(s)
  if isinstance(d,dict) and 'tree' in d:tr=d.get('truncated');matches=[x['path'] for x in d['tree'] if pat.search(x['path'])]
  else:matches=[t[:1600] for t in s.splitlines() if pat.search(t)]
 except:matches=[t[:1600] for t in s.splitlines() if pat.search(t)]
 out[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'truncated':tr,'matches':matches}
(L/'cached-registry-screen.json').write_text(json.dumps(out,indent=2))
for p,d in out.items():
 if d['matches']:print(pathlib.Path(p).name, '\n'+'\n'.join(d['matches'][:20]))
(L/'registry-status.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'live_api':'Not retried: explicit user report of GitHub API 403 rate limit. Current HEAD clearance HOLD.','known_heads':{'openai':'4eaee87548250b2682affda7d05d947c05554bae','omega_latest_user_receipt':'622593005d2dd18d37a84559855df25e18fa2c3c','leanpool':'01db1d7049cf9668bda1e9e106875ee1278b43e6'},'limits':'Cached complete subtrees, raw candidate indexes and projects.yml screened. Truncated recursive roots do not confer clearance; no nonfinding is novelty proof.'},indent=2))
