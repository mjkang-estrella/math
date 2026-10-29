import pathlib,json,re,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent;B=L.parent
pattern=re.compile(r'2510[.]09206|truncated.?exponential|r[eé]nyi|log.?concav|entropy.?increment|reverse.?young|fu.{0,4}li',re.I)
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'delta':{},'inventories':{}}
d=json.loads((L/'omega-delta.json').read_text());fs=d['files'];cs=d['commits']
out['delta']={'base':d['base_commit']['sha'],'head':d['commits'][-1]['sha'],'status':d['status'],'total_commits':d['total_commits'],'returned_commits':len(cs),'files':len(fs),'below_300_cap':len(fs)<300,'semantic_hits':[],'missing_patches':[],'commit_chronology':[{'sha':c['sha'],'committer':c['commit']['committer']['date'],'message':c['commit']['message'][:250]} for c in cs]}
for f in fs:
 if 'patch' not in f:out['delta']['missing_patches'].append(f['filename'])
 hits=[x[:500] for x in f.get('patch','').splitlines() if pattern.search(x)]
 if hits:out['delta']['semantic_hits'].append({'path':f['filename'],'lines':hits[:12]})
for name in ['omega','openai']:
 p=B/'root-edge-irregulator-final-freeze-r1'/(name+'-tree.txt');h=hashlib.sha256();count=0;hits=[]
 with p.open('rb') as f:
  for b in f:
   h.update(b);count+=1;s=b.decode(errors='replace').rstrip()
   if pattern.search(s):hits.append(s)
 out['inventories'][name]={'path':str(p),'sha256':h.hexdigest(),'lines':count,'path_hits':hits,'limitation':'Path screen only; historical cache path inventory, not semantic absence or current complete tree.'}
(L/'registry-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'delta_files':len(fs),'missing_patches':len(out['delta']['missing_patches']),'hits':out['delta']['semantic_hits'],'inventories':{k:{'lines':v['lines'],'sha256':v['sha256'],'hits':len(v['path_hits'])} for k,v in out['inventories'].items()}},indent=2))
