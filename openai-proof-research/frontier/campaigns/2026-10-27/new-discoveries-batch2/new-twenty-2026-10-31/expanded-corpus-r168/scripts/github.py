import pathlib,json,urllib.request,urllib.parse,time,datetime,hashlib
D=pathlib.Path(__file__).resolve().parents[1];p=D/'sources/github';p.mkdir(exist_ok=True)
qs=['"2212.03100" lean','"secure domination" lean','"Balogh" "hypergraph" lean','"Rowland" "binary" lean','"Vanishing Ones" lean','"Winter" "polytope" lean','"Frankl" "lexicographic" lean','"12-representable" lean'];out=[]
for j,q in enumerate(qs):
 u='https://api.github.com/search/repositories?q='+urllib.parse.quote(q);r={'query':q,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=15) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest());(p/f'{j}.json').write_bytes(b);o=json.loads(b);r.update(total_count=o.get('total_count'),hits=[x['full_name'] for x in o.get('items',[])])
 except Exception as e:r['error']=str(e);out.append(r);break
 out.append(r);(D/'outputs/github-screen.json').write_text(json.dumps(out,indent=2));print(r,flush=True);time.sleep(8)
(D/'outputs/github-screen.json').write_text(json.dumps(out,indent=2))
