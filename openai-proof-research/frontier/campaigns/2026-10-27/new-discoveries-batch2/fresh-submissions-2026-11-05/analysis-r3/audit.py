import json,pathlib,hashlib,re,subprocess,datetime
b=pathlib.Path(__file__).parent.parent;o=b/'analysis-r3';pat=re.compile(r'325507|347029|374935|352819|1305[.]0612|2006[.]14985|2605[.]25271|2112[.]01462|signed.mean.value|herda|mirrahimi|shifted.binomial|pl[uü].cker|hadamard.type',re.I)
r=json.load(open(b/'analysis-r2/registry-reuse-screen.json'));rows=[]
for x in r['cached_bodies']:
 p=pathlib.Path(x['path'])
 if not p.exists():continue
 t=p.read_text(errors='replace');hits=[line[:350] for line in t.splitlines() if pat.search(line)]
 rows.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'hits':hits[:30]})
indexes=[]
for x in r['immutable_listings']:
 p=pathlib.Path(x['index']);data=json.load(open(p));t=p.read_text(); indexes.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'hits':[l[:400] for l in t.splitlines() if pat.search(l)][:100]})
commands=[['git','log','--all','--format=%H %s','--extended-regexp','--regexp-ignore-case','--grep=325507|347029|374935|352819|signed.mean.value|mirrahimi|herda|shifted.binomial'],['git','rev-list','--all','--objects']]
history=[]
for c in commands:
 z=subprocess.run(c,capture_output=True,text=True);ls=z.stdout.splitlines();history.append({'command':c,'exit':z.returncode,'lines':len(ls),'hits':[l for l in ls if pat.search(l)][:100],'stdout_sha256':hashlib.sha256(z.stdout.encode()).hexdigest()})
(o/'registry-history.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bodies':rows,'indexes':indexes,'all_ref':history,'omega_delta':'HOLD; no API retry'},indent=2));print('bodies',len(rows),'bodyhits',[(x['path'],x['hits']) for x in rows if x['hits']],'indexes',indexes,'history',history)
