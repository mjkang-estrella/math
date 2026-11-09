import pathlib,json,hashlib,os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(15,15));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
p=pathlib.Path(__file__).resolve().parent
head=json.loads((p/'sources/registry-head.json').read_text())['sha'];old=json.loads((p.parent/'fresh-corpus-r19/registry-screen.json').read_text());refs=[]
for d in old['reused']:
 f=pathlib.Path(d['path']);sha=hashlib.sha256(f.read_bytes()).hexdigest();assert sha==d['sha256'];refs.append({'path':str(f),'sha256':sha,'verified':True})
tree=json.loads(pathlib.Path(refs[1]['path']).read_text());assert not tree['truncated']
terms=['gammoid','superconcentrator','Bene','queens','denominator','edge-color','edge_col','nearly-bipartite','tidy','Hamada','Weil','tree-embedding','hereditary','Schur','projective-plane','supertree','S-Diophantine','two-thinning']
hits={t:[x['path'] for x in tree['tree'] if t.lower() in x['path'].lower()] for t in terms}
(p/'registry-screen.json').write_text(json.dumps({'head':head,'unchanged':head==old['head'],'reused_hash_verified':refs,'truncated':tree['truncated'],'terms':terms,'hits':hits,'scope':'Complete preprints path screen only. No assertion of full body reading, no worldwide novelty clearance. MathDB/Palomar inherited403 not retried.'},indent=2)+'\n')
print(head,{k:len(v) for k,v in hits.items()})
