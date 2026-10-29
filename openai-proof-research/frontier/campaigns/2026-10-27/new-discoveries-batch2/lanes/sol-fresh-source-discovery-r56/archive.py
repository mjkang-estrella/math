import pathlib,json,hashlib,datetime,shutil
P=pathlib.Path(__file__).resolve().parent;C=P.parent.parent
context=[C.parents[3]/'AGENTS.md',C/'AGENTS.md',C/'ledger.json',C/'prior-campaign-context.json',C/'NEXT.md']
# Ancestor located explicitly to avoid depending on relative-depth assumptions.
context[0]=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md')
for s in ['sol-fresh-source-discovery-r52','sol-fresh-source-discovery-r54','sol-fresh-source-discovery-r55','sol-fresh-discrete-algebra-r23']:
 context.append(P.parent/s/'SUMMARY.md')
out={}
for f in context:
 b=f.read_bytes();out[str(f)]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(P/'context-screen.json').write_text(json.dumps(out,indent=2)+'\n')
paths=[('omega-D5.json','sol-fresh-source-discovery-r54/sources/current-omega-D5.json'),('omega-Problems.json','sol-fresh-source-discovery-r54/sources/current-omega-Problems.json'),('omega-main-tree.json','sol-fresh-source-discovery-r49/sources/omega-main-tree.json'),('openai-preprints.json','sol-fresh-source-discovery-r49/sources/openai-preprints.json'),('aim-tree.json','sol-fresh-source-discovery-r49/sources/aim-tree.json'),('count-tree.json','sol-fresh-source-discovery-r49/sources/count-tree.json')]
rows=[]
for name,old in paths:
 f=P.parent/old;dest=P/'sources'/name;shutil.copyfile(f,dest);data=dest.read_bytes();d=json.loads(data)
 hits=[x for x in d['tree'] if any(w in x['path'].lower() for w in ['bootstrap','percolation','spanoid','spanning-set','spanning_set'])]
 rows.append({'file':'sources/'+name,'reused_from':str(f),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'entries':len(d['tree']),'truncated':d.get('truncated'),'lexical_hits':hits})
(P/'registry-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scopes':rows,'omega_delta':'3 commits, 1 documentation file; no D5/Problems tree paths changed from r54 baseline; full-dev coverage NOT claimed','limits':'Lexical scope only; no exhaustive semantic prior-art clearance. r54 exact refreshed scopes supersede its stale inherited scopes metadata.'},indent=2)+'\n')
