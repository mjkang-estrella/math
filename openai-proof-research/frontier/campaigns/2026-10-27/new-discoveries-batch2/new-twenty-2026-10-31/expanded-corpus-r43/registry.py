import pathlib,json,hashlib,urllib.request,datetime,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
w=pathlib.Path(__file__).resolve().parent; old=w.parent/'expanded-corpus-r42/registry-screen.json';d=json.loads(old.read_text());p=pathlib.Path(d['openai_preprints_reuse']['path']);b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==d['openai_preprints_reuse']['sha256'];t=json.loads(b)
terms=['Sperner','sign-variation','amplituhedron','fractional','transversal','path-cover','chordal','350625','350316','350596']
hits=[x['path'] for x in t['tree'] if any(q.lower() in x['path'].lower() for q in terms)]
url='https://api.github.com/repos/the-omega-institute/trureturing/compare/bbae308affe6bde46be6cbdb01ec9efa8c47411f...e562ed8d063d3a029bd3576969710e8fa28dc751'
r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=30) as f:
  b=f.read();(w/'sources/omega-diff.json').write_bytes(b);r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest());od=json.loads(b);r['paths']=[x['filename'] for x in od.get('files',[])]
except Exception as e:r['error']=str(e)
(w/'registry-screen.json').write_text(json.dumps({'openai_head':'4eaee87548250b2682affda7d05d947c05554bae','complete_preprints_index':d['openai_preprints_reuse'],'terms':terms,'path_hits':hits,'omega_compare':r,'limitation':'Navigation only, no proof-body clearance. Omega changed files not automatically excluded.'},indent=2)+'\n');print(json.dumps({'hits':hits,'omega':r},indent=2))
