import pathlib,json,hashlib,re,datetime
O=pathlib.Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();files=[O.parent/'fresh-corpus-r10/sources/registry-preprints.json',O.parent/'fresh-corpus-r10/sources/registry-preprints-receipt.json',O.parent/'fresh-corpus-r8/sources/registry-current.json'];refs=[]
for p in files:refs.append(dict(path=str(p),sha256=H(p.read_bytes())))
head=json.loads((O/'sources/registry-head.json').read_text())['sha'];assert head=='4eaee87548250b2682affda7d05d947c05554bae'
a=json.loads(files[0].read_text());assert a['sha']=='3f56f68a176b4494c346091ea0a319651bc217ec' and not a.get('truncated',False)
b=json.loads((O/'sources/omega-tree.json').read_text());patterns=['383930','383944','384169','trifocal','Coxeter','FRegular','FPure','F-Regular','F-Pure','boundary','braid','Hitchin','TropicalHilbert']
res={}
for name,z in [('openai_preprints',a),('omega_current_tree',b)]:
 paths=[x['path'] for x in z['tree']];res[name]={'entries':len(paths),'truncated':z.get('truncated'),'sha':z['sha'],'matches':{k:[p for p in paths if k.lower() in p.lower()] for k in patterns}}
(O/'registry-screen.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),reused_files=refs,openai_current_head=head,screen=res,limits='Bounded path search, not body clearance. OpenAI root tree truncated and unused as complete inventory. MathDB/Palomar inherited403 retained; no requests. Omega tree completeness only if truncated=false; no universal novelty claim.'),indent=2)+'\n');print(json.dumps({k:{'entries':v['entries'],'truncated':v['truncated'],'nonempty':{p:len(t) for p,t in v['matches'].items() if t}} for k,v in res.items()},indent=2))
